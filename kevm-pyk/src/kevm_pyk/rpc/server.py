import logging
import sys
from argparse import ArgumentParser
from pathlib import Path
from typing import Any, Final, Literal

import gevent
import gevent.pywsgi
import gevent.queue
from pyk.cli_utils import check_dir_path, dir_path, loglevel
from tinyrpc.dispatch import RPCDispatcher
from tinyrpc.protocols.jsonrpc import JSONRPCProtocol
from tinyrpc.server.gevent import RPCServer, RPCServerGreenlets
from tinyrpc.transports.wsgi import WsgiServerTransport

from .controller import FoundryController

LOGGER: Final = logging.getLogger(__name__)
LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'
DEFAULT_SERVER_HOST: Final = 'localhost'
DEFAULT_SERVER_PORT: Final = 43242


class FoundryServer:
    _server: RPCServer

    def __init__(self, host: str, port: int, foundry_out: Path) -> None:
        check_dir_path(foundry_out)

        transport = WsgiServerTransport(queue_class=gevent.queue.Queue)
        wsgi_server = gevent.pywsgi.WSGIServer((host, port), transport.handle)
        gevent.spawn(wsgi_server.serve_forever)

        controller = FoundryController(foundry_out)

        dispatcher = RPCDispatcher()
        dispatcher.register_instance(controller)
        server = RPCServerGreenlets(transport, JSONRPCProtocol(), dispatcher)
        server.trace = self._log_trace

        self._server = server

    @staticmethod
    def _log_trace(direction: Literal['<-', '->'], context: Any, message: bytes) -> None:
        LOGGER.debug('%s %s', direction, message)

    def serve_forever(self) -> None:
        self._server.serve_forever()


def main() -> None:
    sys.setrecursionlimit(15000000)
    args = _argument_parser().parse_args()

    logging.basicConfig(level=args.level, format=LOG_FORMAT)

    LOGGER.info(f'Starting KEVM Foundry Server at: {args.host}:{args.port}')
    server = FoundryServer(host=args.host, port=args.port, foundry_out=args.foundry_out)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        ...
    LOGGER.info('Stopped KEVM Foundry Server')


def _argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='KEVM Foundry Server')
    parser.add_argument('foundry_out', type=dir_path, help='path to Foundry output directory')
    parser.add_argument(
        '-l',
        '--level',
        metavar='LEVEL',
        type=loglevel,
        default=loglevel('error'),
        help='logging level (default: error)',
    )
    parser.add_argument(
        '-s',
        '--host',
        metavar='HOST',
        default=DEFAULT_SERVER_HOST,
        help=f'server host (default: {DEFAULT_SERVER_HOST})',
    )
    parser.add_argument(
        '-p',
        '--port',
        metavar='PORT',
        type=int,
        default=DEFAULT_SERVER_PORT,
        help=f'server port (default: {DEFAULT_SERVER_PORT})',
    )
    return parser


if __name__ == '__main__':
    main()
