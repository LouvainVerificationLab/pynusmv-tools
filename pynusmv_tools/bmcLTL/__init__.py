"""
The objective of the tool implemented in :mod:`pynusmv_tools.bmcLTL` is to 
demonstrate with a simple example (LTL) how one can use the bmc additions 
to PyNuSMV to develop verification tools for new logic formalisms. Hence, 
the approach that was adopted in that context was to *NOT* use any of the 
"higher level services" and develop a verification tool translating 
"literally" the reduction of that logic to a propositional SAT problem as 
imagined or stated in a reference paper.

In this scope, the reference paper that was used was:

            Biere et al - ``Bounded Model Checking'' - 2003  
"""
__all__ = ['parsing', 'ast', 'gen', 'check']