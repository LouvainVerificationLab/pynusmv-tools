import unittest

from pynusmv.dd import BDD
from pynusmv.init import init_nusmv, deinit_nusmv
from pynusmv.mc import eval_simple_expression

from pynusmv_tools.mas import glob

from pynusmv_tools.atlk_irf import check
from pynusmv_tools.atlkFO.parsing import parseATLK


class TestCheckPartial(unittest.TestCase):
    
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
        
    def cardgame(self):
        glob.load_from_file("tests/pynusmv_tools/atlkPO/models/cardgame.smv")
        fsm = glob.mas()
        self.assertIsNotNone(fsm)
        return fsm
        
    def cardgame_fair(self):
        glob.load_from_file("tests/pynusmv_tools/atlkPO/models/cardgame-fair.smv")
        fsm = glob.mas()
        self.assertIsNotNone(fsm)
        return fsm
        
    def cardgame_post_fair(self):
        glob.load_from_file("tests/pynusmv_tools/atlkPO/models/cardgame-post-fair.smv")
        fsm = glob.mas()
        self.assertIsNotNone(fsm)
        return fsm
        
    def trans2_fair(self):
        glob.load_from_file(
                           "tests/pynusmv_tools/atlkPO/models/2-transmission-fair.smv")
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
        
    def transmission_fair(self):
        glob.load_from_file("tests/pynusmv_tools/atlkPO/models/transmission-fair.smv")
        fsm = glob.mas()
        self.assertIsNotNone(fsm)
        return fsm
    
    def transmission_post_fair(self):
        glob.load_from_file(
                        "tests/pynusmv_tools/atlkPO/models/transmission-post-fair.smv")
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
        
        self.assertTrue(check(fsm, parseATLK("K<'player'>'pcard=none' & K<'player'>'dcard=none'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~(K<'player'> 'dcard=Ac' | K<'player'> 'dcard=K' | K<'player'> 'dcard=Q'))")[0], implementation="partial", pre_filtering=False))
        
        self.assertTrue(check(fsm, parseATLK("<'dealer'> X 'pcard=Ac'")[0], implementation="partial", pre_filtering=False))
        self.assertFalse(check(fsm, parseATLK("<'dealer'> G ~'win'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("['player'] X 'pcard=Ac'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("['dealer'] F 'win'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~<'player'> X 'win')")[0], implementation="partial", pre_filtering=False))
        self.assertFalse(check(fsm, parseATLK("<'player'> F 'win'")[0], implementation="partial", pre_filtering=False))
        
        self.assertTrue(check(fsm, parseATLK("EG ~'win'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("EF 'win'")[0], implementation="partial", pre_filtering=False))
        self.assertFalse(check(fsm, parseATLK("AF 'win'")[0], implementation="partial", pre_filtering=False))
        
    
    @unittest.expectedFailure # MC algo does not deal with fairness on action for now
    def test_cardgame_fair(self):
        fsm = self.cardgame_fair()
        
        self.assertTrue(check(fsm, parseATLK("K<'player'>'pcard=none' & K<'player'>'dcard=none'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~(K<'player'> 'dcard=Ac' | K<'player'> 'dcard=K' | K<'player'> 'dcard=Q'))")[0], implementation="partial", pre_filtering=False))
        
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~<'player'> X 'win')")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("['player'] X 'pcard=Ac'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'dealer'> X 'pcard=Ac'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'dealer'> G ~'win'")[0], implementation="partial", pre_filtering=False))
        self.assertFalse(check(fsm, parseATLK("['dealer'] F 'win'")[0], implementation="partial", pre_filtering=False))
        
        # Player can win
        self.assertTrue(check(fsm, parseATLK("<'player'> F 'win'")[0], implementation="partial", pre_filtering=False))
        # Dealer can avoid fairness
        self.assertTrue(check(fsm, parseATLK("<'dealer'> F 'FALSE'")[0], implementation="partial", pre_filtering=False))
        
    
    def test_cardgame_post_fair(self):
        fsm = self.cardgame_post_fair()
        
        self.assertTrue(check(fsm, parseATLK("K<'player'>'pcard=none' & K<'player'>'dcard=none'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~(K<'player'> 'dcard=Ac' | K<'player'> 'dcard=K' | K<'player'> 'dcard=Q'))")[0], implementation="partial", pre_filtering=False))
        
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~<'player'> X 'win')")[0]))
        self.assertFalse(check(fsm, parseATLK("['dealer'] F 'win'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("['player'] X 'pcard=Ac'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'dealer'> X 'pcard=Ac'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'dealer'> G ~'win'")[0], implementation="partial", pre_filtering=False))
        
        # Player can win
        self.assertTrue(check(fsm, parseATLK("<'player'> F 'win'")[0], implementation="partial", pre_filtering=False))
        # Dealer can avoid fairness
        self.assertTrue(check(fsm, parseATLK("<'dealer'> F 'FALSE'")[0], implementation="partial", pre_filtering=False))
        

    def test_transmission(self):
        fsm = self.transmission()
        
        self.assertFalse(check(fsm, parseATLK("<'sender'> F 'received'")[0], implementation="partial", pre_filtering=False))
        # False because transmitter cannot win if received is already true
        # and he has no clue about it
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> G ~'received'")[0], implementation="partial", pre_filtering=False))
        self.assertFalse(check(fsm, parseATLK("<'sender'> X 'received'")[0], implementation="partial", pre_filtering=False))
        # False because transmitter cannot win if received is already true
        # and he has no clue about it
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> X ~'received'")[0], implementation="partial", pre_filtering=False))
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> F 'received'")[0], implementation="partial", pre_filtering=False))
        
        # False because the sender does not know if the bit is already
        # transmitted (and in this case, no strategy can avoid 'received')
        self.assertFalse(check(fsm, parseATLK("<'sender'> G ~'received'")[0], implementation="partial", pre_filtering=False))
        
    
    def test_transmission_with_know(self):
        fsm = self.transmission_with_knowledge()
        
        self.assertFalse(check(fsm, parseATLK("<'sender'> F 'received'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> G ~'received'")[0], implementation="partial", pre_filtering=False))
        self.assertFalse(check(fsm, parseATLK("<'sender'> X 'received'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> X ~'received'")[0], implementation="partial", pre_filtering=False))
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> F 'received'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'sender'> G ~'received'")[0], implementation="partial", pre_filtering=False))
    
    
    @unittest.expectedFailure # MC algo does not deal with fairness on action for now
    def test_transmission_fair(self):
        fsm = self.transmission_fair()
        
        self.assertTrue(check(fsm, parseATLK("<'sender'> F 'received'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> G ~'received'")[0], implementation="partial", pre_filtering=False))
        self.assertFalse(check(fsm, parseATLK("<'sender'> X 'received'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> X ~'received'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> F 'received'")[0], implementation="partial", pre_filtering=False))
        
        # False because the sender does not know if the bit is already
        # transmitted (and in this case, no strategy can avoid 'received')
        self.assertFalse(check(fsm, parseATLK("<'sender'> G ~'received'")[0], implementation="partial", pre_filtering=False))
    
    
    def test_transmission_post_fair(self):
        fsm = self.transmission_post_fair()
        
        self.assertTrue(check(fsm, parseATLK("<'sender'> F 'received'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> G ~'received'")[0], implementation="partial", pre_filtering=False))
        self.assertFalse(check(fsm, parseATLK("<'sender'> X 'received'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> X ~'received'")[0], implementation="partial", pre_filtering=False))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> F 'received'")[0], implementation="partial", pre_filtering=False))
        
        # False because the sender does not know if the bit is already
        # transmitted (and in this case, no strategy can avoid 'received')
        self.assertFalse(check(fsm, parseATLK("<'sender'> G ~'received'")[0], implementation="partial", pre_filtering=False))
        
        
    def test_transmission_pre_filtering(self):
        fsm = self.transmission()
        
        # False because transmitter cannot win if received is already true
        # and he has no clue about it
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> G ~'received'")[0], implementation="partial", pre_filtering=True))
        self.assertFalse(check(fsm, parseATLK("<'sender'> X 'received'")[0], implementation="partial", pre_filtering=True))
        # False because transmitter cannot win if received is already true
        # and he has no clue about it
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> X ~'received'")[0], implementation="partial", pre_filtering=True))
        
        # False because the sender does not know if the bit is already
        # transmitted (and in this case, no strategy can avoid 'received')
        self.assertFalse(check(fsm, parseATLK("<'sender'> G ~'received'")[0], implementation="partial", pre_filtering=True))
        
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> F 'received'")[0], implementation="partial", pre_filtering=True))
        self.assertFalse(check(fsm, parseATLK("<'sender'> F 'received'")[0], implementation="partial", pre_filtering=True))
        
    
    def test_transmission_with_know_pre_filtering(self):
        fsm = self.transmission_with_knowledge()
        
        self.assertFalse(check(fsm, parseATLK("<'sender'> F 'received'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> G ~'received'")[0], implementation="partial", pre_filtering=True))
        self.assertFalse(check(fsm, parseATLK("<'sender'> X 'received'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> X ~'received'")[0], implementation="partial", pre_filtering=True))
        self.assertFalse(check(fsm, parseATLK("<'transmitter'> F 'received'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'sender'> G ~'received'")[0], implementation="partial", pre_filtering=True))
        
    
    def test_transmission_post_fair_pre_filtering(self):
        fsm = self.transmission_post_fair()
        
        self.assertTrue(check(fsm, parseATLK("<'sender'> F 'received'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> G ~'received'")[0], implementation="partial", pre_filtering=True))
        self.assertFalse(check(fsm, parseATLK("<'sender'> X 'received'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> X ~'received'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'transmitter'> F 'received'")[0], implementation="partial", pre_filtering=True))
        
        # False because the sender does not know if the bit is already
        # transmitted (and in this case, no strategy can avoid 'received')
        self.assertFalse(check(fsm, parseATLK("<'sender'> G ~'received'")[0], implementation="partial", pre_filtering=True))
        
        
    def test_cardgame_pre_filtering(self):
        fsm = self.cardgame()
        
        self.assertTrue(check(fsm, parseATLK("<'dealer'> X 'pcard=Ac'")[0], implementation="partial", pre_filtering=True))
        self.assertFalse(check(fsm, parseATLK("<'dealer'> G ~'win'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~<'player'> X 'win')")[0], implementation="partial", pre_filtering=True))
        self.assertFalse(check(fsm, parseATLK("<'player'> F 'win'")[0], implementation="partial", pre_filtering=True))
        
        self.assertTrue(check(fsm, parseATLK("['player'] X 'pcard=Ac'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("['dealer'] F 'win'")[0], implementation="partial", pre_filtering=True))
        
        
    def test_cardgame_post_fair_pre_filtering(self):
        fsm = self.cardgame_post_fair()
        
        self.assertTrue(check(fsm, parseATLK("K<'player'>'pcard=none' & K<'player'>'dcard=none'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~(K<'player'> 'dcard=Ac' | K<'player'> 'dcard=K' | K<'player'> 'dcard=Q'))")[0], implementation="partial", pre_filtering=True))
        
        self.assertTrue(check(fsm, parseATLK("AG('step = 1' -> ~<'player'> X 'win')")[0], implementation="partial", pre_filtering=True))
        self.assertFalse(check(fsm, parseATLK("['dealer'] F 'win'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("['player'] X 'pcard=Ac'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'dealer'> X 'pcard=Ac'")[0], implementation="partial", pre_filtering=True))
        self.assertTrue(check(fsm, parseATLK("<'dealer'> G ~'win'")[0], implementation="partial", pre_filtering=True))
        
        # Player can win
        self.assertTrue(check(fsm, parseATLK("<'player'> F 'win'")[0], implementation="partial", pre_filtering=True))
        # Dealer can avoid fairness
        self.assertTrue(check(fsm, parseATLK("<'dealer'> F 'FALSE'")[0], implementation="partial", pre_filtering=True))
