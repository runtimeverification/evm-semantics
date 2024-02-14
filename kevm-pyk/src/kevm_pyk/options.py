from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterable

    from pyk.kore.rpc import FallbackReason
    from pyk.utils import BugReport

@dataclass(frozen=True)
class ProveOptions:
    auto_abstract_gas: bool
    bug_report: BugReport | None
    max_depth: int
    break_every_step: bool
    break_on_jumpi: bool
    break_on_calls: bool
    break_on_storage: bool
    break_on_basic_blocks: bool
    workers: int
    counterexample_info: bool
    max_iterations: int | None
    fail_fast: bool
    reinit: bool
    failure_info: bool
    fast_check_subsumption: bool
    always_check_subsumption: bool
    post_exec_simplify: bool
    fallback_on: Iterable[str | FallbackReason] | None
    interim_simplification: int | None

    def __init__(
        self,
        *,
        auto_abstract_gas: bool | None = None,
        bug_report: BugReport | None = None,
        max_depth: int | None = None,
        break_every_step: bool | None = None,
        break_on_jumpi: bool | None = None,
        break_on_calls: bool | None = None,
        break_on_storage: bool | None = None,
        break_on_basic_blocks: bool | None = None,
        workers: int | None = None,
        counterexample_info: bool | None = None,
        max_iterations: int | None = None,
        fail_fast: bool | None = None,
        reinit: bool | None = None,
        failure_info: bool | None = None,
        fast_check_subsumption: bool | None = None,
        always_check_subsumption: bool | None = None,
        post_exec_simplify: bool | None = None,
        fallback_on: Iterable[str | FallbackReason] | None = None,
        interim_simplification: int | None = None,
    ) -> None:
        object.__setattr__(self, 'auto_abstract_gas', bool(auto_abstract_gas))
        object.__setattr__(self, 'bug_report', bug_report)
        object.__setattr__(self, 'max_depth', 1000 if max_depth is None else max_depth)
        object.__setattr__(self, 'break_every_step', bool(break_every_step))
        object.__setattr__(self, 'break_on_jumpi', bool(break_on_jumpi))
        object.__setattr__(self, 'break_on_calls', bool(break_on_calls))
        object.__setattr__(self, 'break_on_storage', bool(break_on_storage))
        object.__setattr__(self, 'break_on_basic_blocks', bool(break_on_basic_blocks))
        object.__setattr__(self, 'workers', 1 if workers is None else workers)
        object.__setattr__(self, 'counterexample_info', True if counterexample_info is None else counterexample_info)
        object.__setattr__(self, 'max_iterations', max_iterations)
        object.__setattr__(self, 'fail_fast', True if fail_fast is None else fail_fast)
        object.__setattr__(self, 'reinit', bool(reinit))
        object.__setattr__(self, 'failure_info', True if failure_info is None else failure_info)
        fast_check_subsumption: bool | None = None,
        object.__setattr__(
            self, 'always_check_subsumption', True if always_check_subsumption is None else always_check_subsumption
        )
        object.__setattr__(self, 'post_exec_simplify', True if post_exec_simplify is None else post_exec_simplify)
        object.__setattr__(self, 'fallback_on', fallback_on)
        object.__setattr__(self, 'interim_simplification', interim_simplification)


@dataclass(frozen=True)
class RPCOptions:
    use_booster: bool
    kore_rpc_command: tuple[str, ...]
    smt_timeout: int | None
    smt_retry_limit: int | None
    smt_tactic: str | None
    trace_rewrites: bool
    port: int | None
    maude_port: int | None

    def __init__(
        self,
        *,
        use_booster: bool | None = None,
        kore_rpc_command: str | Iterable[str] | None = None,
        smt_timeout: int | None = None,
        smt_retry_limit: int | None = None,
        smt_tactic: str | None = None,
        trace_rewrites: bool | None = None,
        port: int | None = None,
        maude_port: int | None = None,
    ) -> None:
        if kore_rpc_command is None:
            kore_rpc_command = (
                ('kore-rpc-booster',) if (True if use_booster is None else use_booster) else ('kore-rpc',)
            )
        elif isinstance(kore_rpc_command, str):
            kore_rpc_command = (kore_rpc_command,)
        else:
            kore_rpc_command = tuple(kore_rpc_command)
        object.__setattr__(self, 'use_booster', True if use_booster is None else use_booster)
        object.__setattr__(self, 'kore_rpc_command', kore_rpc_command)
        object.__setattr__(self, 'smt_timeout', smt_timeout)
        object.__setattr__(self, 'smt_retry_limit', smt_retry_limit)
        object.__setattr__(self, 'smt_tactic', smt_tactic)
        object.__setattr__(self, 'trace_rewrites', bool(trace_rewrites))
        object.__setattr__(self, 'port', port)
        object.__setattr__(self, 'maude_port', maude_port)
