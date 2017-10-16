from . import ChoiceError, ExclusiveChoiceError
from copy import deepcopy
from .graph import domaintuple

def Obligation(fsm, state, formula, context):
    return domaintuple(fsm=fsm, state=state, formula=formula, context=context)

class Explanation:
    """
    An explanation is composed of
     * a graph;
     * an initial node of the graph;
     * a subset of unexplained nodes of the graph.
    """
    
    def __init__(self, graph, initial, unexplained, translated, untranslated):
        """
        Create a new explanation based on graph, with initial as the initial
        obligation, and unexplained as the set of unexplained obligations.
        untranslated is the untranslated version of graph.
        
        graph -- the graph of the explanation;
        initial -- the initial obligation of graph;
        unexplained -- the subset of obligations that are unexplained;
        translated -- the set of translated obligations;
        untranslated -- the untranslated version of graph.
        """
        self.graph = graph
        self.initial = initial
        self.unexplained = unexplained
        self.translated = translated
        self.untranslated = untranslated
    
    def dot(self):
        """
        Return a dot encoding of this explanation graph.
        """
        def node(n):
            extension = {}
            if n == self.initial:
                extension["initial"] = True
            if n in self.unexplained:
                extension["unexplained"] = True
            return extension
        graph = self.graph.extension(node_extension=node)
        return graph.dot()
    
    def expanded(self, node, attributors=None, choosers=None):
        """
        Return a new explanation where the given unexplained node is expanded.
        
        node -- a node of this explanation's unexplained nodes;
        attributors -- if not None, a list of attributors.
        choosers -- if not None, a list of choosers.
        
        If attributors are given, these attributors are called before calling
        formulas attributors.
        If choosers are given, these choosers are called before calling
        formulas choosers.
        """
        return node.formula.explain(node.fsm,
                                    node.state,
                                    node.context,
                                    attributors=attributors,
                                    choosers=choosers,
                                    expand=self)