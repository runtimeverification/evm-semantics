import json
import sys
from typing import Any


def print_kast(data: Any) -> None:
    if isinstance(data, list):
        sys.stdout.write('`JSONList`(')
        for elem in data:
            sys.stdout.write('`JSONs`(')
            print_kast(elem)
            sys.stdout.write(',')
        sys.stdout.write('`.List{"JSONs"}`(.KList)')
        for _ in data:
            sys.stdout.write(')')
        sys.stdout.write(')')
    elif isinstance(data, dict):
        sys.stdout.write('`JSONObject`(')
        for key, value in data.items():
            sys.stdout.write('`JSONs`(`JSONEntry`(')
            print_kast(key)
            sys.stdout.write(',')
            print_kast(value)
            sys.stdout.write('),')
        sys.stdout.write('`.List{"JSONs"}`(.KList)')
        for _ in data:
            sys.stdout.write(')')
        sys.stdout.write(')')
    elif isinstance(data, str):
        sys.stdout.write('#token('),
        sys.stdout.write(json.dumps(json.dumps(data)))
        sys.stdout.write(',"String")')
    elif isinstance(data, int):
        sys.stdout.write('#token("'),
        sys.stdout.write(str(data))
        sys.stdout.write('","Int")')
    else:
        sys.stdout.write(str(type(data)))
        raise AssertionError


def main() -> None:
    filename = sys.argv[1]

    with open(filename) as data_file:
        data = json.load(data_file)
    print_kast(data)
    print()


if __name__ == '__main__':
    main()
