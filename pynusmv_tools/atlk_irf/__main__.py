import argparse
import sys
import os
import importlib
import tempfile

from pyparsing import ParseException

from pynusmv.exception import PyNuSMVError
from pynusmv.dd import enable_dynamic_reordering
from pynusmv.init import init_nusmv

from pynusmv_tools.mas import glob
from pynusmv_tools.atlkFO.parsing import parseATLK
from . import check as checkATLK


def main():
    """
    Process specs on the given NuSMV model.

    Build the model from a given file and check the given ATLK_irF
    specifiation.
    """
    sys.setrecursionlimit(100000)

    # Parse arguments
    parser = argparse.ArgumentParser(description='ATLK_irF model checker.')
    # Populate arguments:
    # size of the model, property, variant
    parser.add_argument('-m', dest='model',
                        help='the module to generate models '
                             '(an SMV text model, '
                             'or a python module with a "model()" function, '
                             'and an optional "agents()" function)',
                        required=True)
    parser.add_argument('-p', dest='property', help='the property to check',
                        required=True)
    parser.add_argument('-i', dest='implementation',
                        help='the implementation to use '
                             '(naive, partial, early, symbolic, backward)'
                             ' (default: naive)',
                        default="naive")

    parser.add_argument('-pf', dest='filtering',
                        help='activate pre-filtering (default: deactivated)',
                        action='store_true', default=False)

    # Variables-order-related arguments
    parser.add_argument('-rbdd-order', dest="initial_ordering",
                        help="specify an initial variables order file",
                        default=None)
    parser.add_argument('-no-rbdd', dest="reordering",
                        help='deactivate BDD variables reordering '
                             '(default: activated)',
                        action='store_false', default=True)
    parser.add_argument('-rbdd-method', dest="reordering_method",
                        help='choose BDD variables reordering method '
                             '(default: sift)', default="sift")

    args = parser.parse_args(sys.argv[1:])

    check = lambda mas, formula: checkATLK(mas,
                                           formula,
                                           implementation=args.implementation,
                                           pre_filtering=args.filtering)

    # Check
    with tempfile.NamedTemporaryFile(suffix=".smv") as tmp:
        # Generate the model
        try:
            mod = importlib.import_module(args.model)
            tmp.write(mod.model().encode("UTF-8"))
        except ImportError:
            mod = None
            with open(args.model, "r") as f:
                tmp.write(f.read().encode("UTF-8"))
        tmp.flush()
        MODELFILE = tmp.name

        # Load the file in PyNuSMV
        with init_nusmv():
            # Set dynamic reordering on
            if args.reordering:
                enable_dynamic_reordering(method=args.reordering_method)
        
            glob.load_from_file(MODELFILE)
        
            # Build the model
            if mod is not None and hasattr(mod, "agents"):
                agents = mod.agents()
            else:
                agents = None
            mas = glob.mas(agents=agents,
                           initial_ordering=args.initial_ordering)
        
            # Check the property
            spec = parseATLK(args.property)[0]
        
            # Measure execution time and save it
            print(str(spec) + ' is ' + str(check(mas, spec)))
        
            # Close PyNuSMV
            glob.reset_globals()


if __name__ == "__main__":
    main()