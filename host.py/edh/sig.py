import sys, signal, faulthandler
import asyncio

__all__ = ["dump_stacks_on_SIGQUIT"]


def dump_stacks_on_SIGQUIT():
    try:
        signal.signal(signal.SIGQUIT, dump_stacks)
    except AttributeError:
        pass


def dump_stacks(signum, frame):

    faulthandler.dump_traceback(file=sys.stderr, all_threads=True)

    dump_aio_task_stacks()


def dump_aio_task_stacks():
    for aiot in asyncio.Task.all_tasks():
        print("", file=sys.stderr)
        aiot.print_stack(file=sys.stderr)
