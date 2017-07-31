import unittest

from pynusmv.dd import BDD
from pynusmv.init import init_nusmv, deinit_nusmv
from pynusmv.mc import eval_simple_expression

from pynusmv_tools.mas import glob

from pynusmv_tools.atlk_irf import check
from pynusmv_tools.atlkFO.parsing import parseATLK


class TestCheckBackward(unittest.TestCase):
    
    def setUp(self):
        init_nusmv()
    
    def tearDown(self):
        glob.reset_globals()
        deinit_nusmv()
    
    
    def little(self):
        glob.load_from_file("tests/pynusmv_tools/atlkPO/models/little.smv")
        fsm = glob.mas()
        self.assertIsNotNone(fsm)
        return fsm
    
    
    def little2(self):
        glob.load_from_file("tests/pynusmv_tools/atlkPO/models/little2.smv")
        fsm = glob.mas()
        self.assertIsNotNone(fsm)
        return fsm
        
    def cardgame(self):
        glob.load_from_file("tests/pynusmv_tools/atlkPO/models/cardgame.smv")
        fsm = glob.mas()
        self.assertIsNotNone(fsm)
        return fsm
        
    def transmission(self):
        glob.load_from_file("tests/pynusmv_tools/atlkPO/models/transmission.smv")
        fsm = glob.mas()
        self.assertIsNotNone(fsm)
        return fsm
        
    def transmission_with_knowledge(self):
        glob.load_from_file(
                        "tests/pynusmv_tools/atlkPO/models/transmission-knowledge.smv")
        fsm = glob.mas()
        self.assertIsNotNone(fsm)
        return fsm
        
    def show_si(self, fsm, bdd):
        if bdd.isnot_false():
            sis = fsm.pick_all_states_inputs(bdd)
            print("SI count:", len(sis))
            for si in sis:
                print(si.get_str_values())
            
    def show_s(self, fsm, bdd):
        if bdd.isnot_false():
            for s in fsm.pick_all_states(bdd):
                print(s.get_str_values())
            
    def show_i(self, fsm, bdd):
        if bdd.isnot_false():
            for i in fsm.pick_all_inputs(bdd):
                print(i.get_str_values())
        
        
    def test_cardgame(self):
        fsm = self.cardgame()
        
        self.assertTrue(check(fsm, parseATLK("K<'player'>'pcard=none' & K<'player'>'dcard=none'")[0], implementation="backward"))
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~(K<'player'> 'dcard=Ac' | K<'player'> 'dcard=K' | K<'player'> 'dcard=Q'))")[0], implementation="backward"))
        
        self.assertTrue(check(fsm, parseATLK("<'dealer'> X 'pcard=Ac'")[0], implementation="backward"))
        self.assertTrue(check(fsm, parseATLK("['player'] X 'pcard=Ac'")[0], implementation="backward"))
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~<'player'> X 'win')")[0], implementation="backward"))
        self.assertFalse(check(fsm, parseATLK("<'player'> F 'win'")[0], implementation="backward"))
        
        self.assertTrue(check(fsm, parseATLK("EG ~'win'")[0], implementation="backward"))
        self.assertTrue(check(fsm, parseATLK("EF 'win'")[0], implementation="backward"))
        self.assertFalse(check(fsm, parseATLK("AF 'win'")[0], implementation="backward"))
        
        
    def test_cardgame_dealer_x_pcard(self):
        fsm = self.cardgame()
        self.assertTrue(check(fsm, parseATLK("<'dealer'> X 'pcard=Ac'")[0], implementation="backward"))
        

    def test_transmission(self):
        fsm = self.transmission()
        
        self.assertFalse(check(fsm, parseATLK("<'sender'> F 'received'")[0], implementation="backward"))
        # False because transmitter cannot win if received is already true
        # and he has no clue about it
        self.assertFalse(check(fsm, parseATLK("<'sender'> X 'received'")[0], implementation="backward"))
        # False because transmitter cannot win if received is already true
        # and he has no clue about it
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> X ~'received'")[0], implementation="backward"))
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> F 'received'")[0], implementation="backward"))
        
    
    def test_transmission_with_know(self):
        fsm = self.transmission_with_knowledge()
        
        self.assertFalse(check(fsm, parseATLK("<'sender'> F 'received'")[0], implementation="backward"))
        self.assertFalse(check(fsm, parseATLK("<'sender'> X 'received'")[0], implementation="backward"))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> X ~'received'")[0], implementation="backward"))
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> F 'received'")[0], implementation="backward"))
    
    def test_little2(self):
        fsm = self.little2()
        
        self.assertTrue(fsm.check_mas())
        self.assertTrue(check(fsm, parseATLK("<'agent'> F 'o = 3'")[0], implementation="naive"))
        self.assertTrue(check(fsm, parseATLK("<'agent'> F 'o = 3'")[0], implementation="partial"))
        self.assertTrue(check(fsm, parseATLK("<'agent'> F 'o = 3'")[0], implementation="early"))
        self.assertTrue(check(fsm, parseATLK("<'agent'> F 'o = 3'")[0], implementation="naive", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'agent'> F 'o = 3'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'agent'> F 'o = 3'")[0], implementation="early", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'agent'> F 'o = 3'")[0], implementation="backward"))
