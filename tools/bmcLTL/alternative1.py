#! /usr/local/bin/python3
"""
This is an alternative implementation which uses the native C api as they were
brought by the the ltlspec module.

Concretely, it uses `ltlspec.generate_ltl_problem` to generate the complete
problem for an LTL verification. (This api fully originates from nusmv).
"""
import sys
import argparse

from pynusmv.init         import init_nusmv
from pynusmv.glob         import load
from pynusmv.bmc.glob     import BmcSupport, master_be_fsm
from pynusmv.parser       import parse_ltl_spec
from pynusmv.node         import Node
from pynusmv.sat          import SatSolverFactory, Polarity, SatSolverResult
from pynusmv.bmc          import ltlspec, utils as bmcutils

def arguments():
    """
    Creates the arguments parser and manages to react to wrong usage.

    :returns: an object having field to store each of the command line arguments
    """
    parser = argparse.ArgumentParser(description="a PyNuSMV backed LTL sat based bmc verifier for LTL")
    parser.add_argument("-v", "--verbose", action="store_true", help="Displays the text of the analyzed model")
    parser.add_argument("-k", "--bound",   type=int, default=10, help="the maximum number of steps in a verified path")
    parser.add_argument("-s", "--spec",    type=str, help="the LTL specification to verify")
    parser.add_argument("-f", "--no-fairness",  help="disable the use of fairness constraints", action="store_true")
    parser.add_argument("-i", "--no-invariants",help="disable the invariants enforcement", action="store_true")
    parser.add_argument("-d", "--dry-run", action="store_true", help="do not perform the verification (no sat solving)")
    parser.add_argument("model", type=str, help="the name of a file containing an SMV model")

    return parser.parse_args()

def check_problem(pb, length):
    fsm    = master_be_fsm()
    cnf    = pb.to_cnf(Polarity.POSITIVE)

    solver = SatSolverFactory.create()
    solver+= cnf
    solver.polarity(cnf, Polarity.POSITIVE)

    if solver.solve() == SatSolverResult.SATISFIABLE:
        cnt_ex = bmcutils.generate_counter_example(fsm, pb, solver, length, "Violation")
        return ("Violation", cnt_ex)
    else:
        return ("Ok", None)

def check_ltl(fml, bound, dry_run):
    import time
    fsm     = master_be_fsm()

    for i in range(bound+1):
        start = time.time()
        problem = ltlspec.generate_ltl_problem(fsm, fml, i)
        end   = time.time()
        if not dry_run:
            status, trace = check_problem(problem, i)
            if status != "Ok":
                return (status, i, trace)
            else:
                print("-- No problem at length {}".format(i))
        else:
            print(" 'Problem {}' ; {}".format(i, end-start))

    return ("Ok", bound, None)

def check(formula, args):
    parsed_fml          = Node.from_ptr(parse_ltl_spec(formula.strip()))
    status,length,trace = check_ltl(parsed_fml, args.bound, args.dry_run)
    if status != 'Ok':
        print("-- {} for length {}".format(status, length))
        print(trace)


def main():
    args = arguments()

    with init_nusmv():
        load(args.model)
        if args.verbose:
            with open(args.model) as f:
                print(f.read())

        with BmcSupport():
            if args.spec is not None:
                check(args.spec, args)
            else:
                print("Enter LTL properties, one per line:")
                for line in sys.stdin:
                    check(line, args)

if __name__ == "__main__":
    main()
