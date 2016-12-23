'''
This module tests the behavior of the functionalities defined in the parsing
module :mod:`pynusmv_tools.bmcLTL.parsing`
'''
from unittest              import TestCase

from pynusmv_tools.bmcLTL          import parsing 

class TestParsing(TestCase):
    
    def test_parse_variable(self):
        ast = parsing.parseLTL("phi")
        self.assertEqual("Proposition(phi)", str(ast))
        
    def test_parse_variable_dotted_name(self):
        ast = parsing.parseLTL("p1.waiting")
        self.assertEqual("Proposition(p1.waiting)", str(ast))
    
    def test_parse_variable_arobase_name(self):
        ast = parsing.parseLTL("p1@waiting")
        self.assertEqual("Proposition(p1@waiting)", str(ast))
        
    def test_parse_variable_specialchar_name(self):
        ast = parsing.parseLTL("p1~waiting")
        # everything from the unknown punctuation on is discarded
        self.assertEqual("Proposition(p1)", str(ast))
    
    def test_parse_variable_containing_TRUE(self):
        ast = parsing.parseLTL("@TRUE")
        # everything from the unknown punctuation on is discarded
        self.assertEqual("Proposition(@TRUE)", str(ast))
        
        ast = parsing.parseLTL("TRUE@")
        # everything from the unknown punctuation on is discarded
        self.assertEqual("Proposition(TRUE@)", str(ast))
        
        ast = parsing.parseLTL("TRUE.")
        # everything from the unknown punctuation on is discarded
        self.assertEqual("Proposition(TRUE.)", str(ast))
        
    def test_parse_variable_containing_FALSE(self):
        ast = parsing.parseLTL("@FALSE")
        # everything from the unknown punctuation on is discarded
        self.assertEqual("Proposition(@FALSE)", str(ast))
        
        ast = parsing.parseLTL("FALSE@")
        # everything from the unknown punctuation on is discarded
        self.assertEqual("Proposition(FALSE@)", str(ast))
        
        ast = parsing.parseLTL("FALSE.")
        # everything from the unknown punctuation on is discarded
        self.assertEqual("Proposition(FALSE.)", str(ast))
    
    def test_parse_constant(self):
        ast = parsing.parseLTL("TRUE")
        self.assertEqual("Constant(TRUE)", str(ast))
        #
        ast = parsing.parseLTL("FALSE")
        self.assertEqual("Constant(FALSE)", str(ast))
        
    def test_parse_number(self):
        # question, shouldn't we reject this instead ?
        ast = parsing.parseLTL("1256")
        self.assertEqual("Constant(1256)", str(ast))
        
    def test_arithmetic_unary_minus(self):
        # number can be negated
        ast = parsing.parseLTL("-12")
        self.assertEqual("Proposition(- (12))", str(ast))
        # and so does a variable
        ast = parsing.parseLTL("-a")
        self.assertEqual("Proposition(- (a))", str(ast))
        # or a nested expression
        ast = parsing.parseLTL("-( 6 * 8)")
        self.assertEqual("Proposition(- ((6) * (8)))", str(ast))
    
    def test_arithmetic_multiplication(self):    
        # numbers 
        ast = parsing.parseLTL("6 * 8")
        self.assertEqual("Proposition((6) * (8))", str(ast))
        # vars
        ast = parsing.parseLTL("a * b")
        self.assertEqual("Proposition((a) * (b))", str(ast))
        # chainable
        ast = parsing.parseLTL("a * b * c")
        self.assertEqual("Proposition((a) * (b) * (c))", str(ast))
        # priority over +/-
        ast = parsing.parseLTL("a + b * c")
        self.assertEqual("Proposition((a) + ((b) * (c)))", str(ast))
        ast = parsing.parseLTL("a * b - c")
        self.assertEqual("Proposition(((a) * (b)) - (c))", str(ast))
    
    def test_arithmetic_division(self):    
        # numbers 
        ast = parsing.parseLTL("6 / 8")
        self.assertEqual("Proposition((6) / (8))", str(ast))
        # vars
        ast = parsing.parseLTL("a / b")
        self.assertEqual("Proposition((a) / (b))", str(ast))
        # chainable
        ast = parsing.parseLTL("a / b / c")
        self.assertEqual("Proposition((a) / (b) / (c))", str(ast))
        # priority over +/-
        ast = parsing.parseLTL("a + b / c")
        self.assertEqual("Proposition((a) + ((b) / (c)))", str(ast))
        ast = parsing.parseLTL("a / b - c")
        self.assertEqual("Proposition(((a) / (b)) - (c))", str(ast))
        
    def test_arithmetic_modulus(self):    
        # numbers 
        ast = parsing.parseLTL("6 mod 8")
        self.assertEqual("Proposition((6) mod (8))", str(ast))
        # vars
        ast = parsing.parseLTL("a mod b")
        self.assertEqual("Proposition((a) mod (b))", str(ast))
        # chainable
        ast = parsing.parseLTL("a mod b mod c")
        self.assertEqual("Proposition((a) mod (b) mod (c))", str(ast))
        # priority over +/-
        ast = parsing.parseLTL("a + b mod c")
        self.assertEqual("Proposition((a) + ((b) mod (c)))", str(ast))
        ast = parsing.parseLTL("a mod b - c")
        self.assertEqual("Proposition(((a) mod (b)) - (c))", str(ast))
        
    def test_arithmetic_multiplicatives_can_be_mixed_at_will(self):
        ast = parsing.parseLTL("a * b / c mod d * b mod a / c")
        self.assertEqual("Proposition((a) * (b) / (c) mod (d) * (b) mod (a) / (c))", str(ast))
        
    def test_arithmetic_addition(self):
        # numbers 
        ast = parsing.parseLTL("6 + 8")
        self.assertEqual("Proposition((6) + (8))", str(ast))
        
        ast = parsing.parseLTL("-6 + 8")
        self.assertEqual("Proposition((- (6)) + (8))", str(ast))
        
        # vars
        ast = parsing.parseLTL("a + b")
        self.assertEqual("Proposition((a) + (b))", str(ast))
        # chainable
        ast = parsing.parseLTL("a + b + c")
        self.assertEqual("Proposition((a) + (b) + (c))", str(ast))
        # priority over <</>>
        ast = parsing.parseLTL("a + b << c")
        self.assertEqual("Proposition(((a) + (b)) << (c))", str(ast))
        ast = parsing.parseLTL("a + b >> c")
        self.assertEqual("Proposition(((a) + (b)) >> (c))", str(ast))
        
    def test_arithmetic_subtraction(self):
        # numbers 
        ast = parsing.parseLTL("6 - 8")
        self.assertEqual("Proposition((6) - (8))", str(ast))
        # vars
        ast = parsing.parseLTL("a - b")
        self.assertEqual("Proposition((a) - (b))", str(ast))
        # chainable
        ast = parsing.parseLTL("a - b - c")
        self.assertEqual("Proposition((a) - (b) - (c))", str(ast))
        # priority over <</>>
        ast = parsing.parseLTL("a - b << c")
        self.assertEqual("Proposition(((a) - (b)) << (c))", str(ast))
        ast = parsing.parseLTL("a - b >> c")
        self.assertEqual("Proposition(((a) - (b)) >> (c))", str(ast))
    
    def test_arithmetic_additives_can_be_mixed_at_will(self):
        ast = parsing.parseLTL("a + b - c - d + b + a - c")
        self.assertEqual("Proposition((a) + (b) - (c) - (d) + (b) + (a) - (c))", str(ast))
        
    def test_arithmetic_lshift(self):
        # numbers 
        ast = parsing.parseLTL("6 << 8")
        self.assertEqual("Proposition((6) << (8))", str(ast))
        # vars
        ast = parsing.parseLTL("a << b")
        self.assertEqual("Proposition((a) << (b))", str(ast))
        # chainable
        ast = parsing.parseLTL("a << b << c")
        self.assertEqual("Proposition((a) << (b) << (c))", str(ast))
        # priority over comparison
        ast = parsing.parseLTL("a << b <= c")
        self.assertEqual("Proposition(((a) << (b)) <= (c))", str(ast))
        ast = parsing.parseLTL("a << b = c")
        self.assertEqual("Proposition(((a) << (b)) = (c))", str(ast))
        
    def test_arithmetic_rshift(self):
        # numbers 
        ast = parsing.parseLTL("6 >> 8")
        self.assertEqual("Proposition((6) >> (8))", str(ast))
        # vars
        ast = parsing.parseLTL("a >> b")
        self.assertEqual("Proposition((a) >> (b))", str(ast))
        # chainable
        ast = parsing.parseLTL("a >> b >> c")
        self.assertEqual("Proposition((a) >> (b) >> (c))", str(ast))
        
        # priority over comparison
        ast = parsing.parseLTL("a >> b <= c")
        self.assertEqual("Proposition(((a) >> (b)) <= (c))", str(ast))
        ast = parsing.parseLTL("a >> b = c")
        self.assertEqual("Proposition(((a) >> (b)) = (c))", str(ast))
        
    def test_shifts_can_be_mixed_at_will(self):
        ast = parsing.parseLTL("a << b << c >> d << b >> a >> c")
        self.assertEqual("Proposition((a) << (b) << (c) >> (d) << (b) >> (a) >> (c))", str(ast))
    
    def test_comparison(self):
        # numbers 
        ast = parsing.parseLTL("6 < 8")
        self.assertEqual("Proposition((6) < (8))", str(ast))
        
        ast = parsing.parseLTL("6 <= 8")
        self.assertEqual("Proposition((6) <= (8))", str(ast))
        
        ast = parsing.parseLTL("6 > 8")
        self.assertEqual("Proposition((6) > (8))", str(ast))
        
        ast = parsing.parseLTL("6 >= 8")
        self.assertEqual("Proposition((6) >= (8))", str(ast))
        
        ast = parsing.parseLTL("6 = 8")
        self.assertEqual("Proposition((6) = (8))", str(ast))
        
        ast = parsing.parseLTL("6 != 8")
        self.assertEqual("Proposition((6) != (8))", str(ast))
        
        # vars
        ast = parsing.parseLTL("a < b")
        self.assertEqual("Proposition((a) < (b))", str(ast))
        
        ast = parsing.parseLTL("a <= b")
        self.assertEqual("Proposition((a) <= (b))", str(ast))
        
        ast = parsing.parseLTL("a > b")
        self.assertEqual("Proposition((a) > (b))", str(ast))
        
        ast = parsing.parseLTL("a >= b")
        self.assertEqual("Proposition((a) >= (b))", str(ast))
        
        ast = parsing.parseLTL("a = b")
        self.assertEqual("Proposition((a) = (b))", str(ast))
        
        ast = parsing.parseLTL("a != b")
        self.assertEqual("Proposition((a) != (b))", str(ast))
        
        # chainable
        ast = parsing.parseLTL("a < b < c")
        self.assertEqual("Proposition((a) < (b) < (c))", str(ast))
        
        ast = parsing.parseLTL("a <= b <= c")
        self.assertEqual("Proposition((a) <= (b) <= (c))", str(ast))
        
        ast = parsing.parseLTL("a > b > c")
        self.assertEqual("Proposition((a) > (b) > (c))", str(ast))
        
        ast = parsing.parseLTL("a >= b >= c")
        self.assertEqual("Proposition((a) >= (b) >= (c))", str(ast))
        
        ast = parsing.parseLTL("a = b = c")
        self.assertEqual("Proposition((a) = (b) = (c))", str(ast))
        
        ast = parsing.parseLTL("a != b != c")
        self.assertEqual("Proposition((a) != (b) != (c))", str(ast))
        
        # mixable
        ast = parsing.parseLTL("a != b < c >= d")
        self.assertEqual("Proposition((a) != (b) < (c) >= (d))", str(ast))
    
    def test_parse_not(self):
        ast = parsing.parseLTL("! phi")
        self.assertEqual("(Not Proposition(phi))", str(ast))
        
        # spacing is irrelevant
        ast = parsing.parseLTL("!phi")
        self.assertEqual("(Not Proposition(phi))", str(ast))
        
        # can be chained
        ast = parsing.parseLTL("! ! ! phi")
        self.assertEqual("(Not (Not (Not Proposition(phi))))", str(ast))
        
        # space is irrelevant (even when chained)
        ast = parsing.parseLTL("!!!phi")
        self.assertEqual("(Not (Not (Not Proposition(phi))))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("!TRUE")
        self.assertEqual("(Not Constant(TRUE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("!(a | b)")
        self.assertEqual("(Not (Proposition(a) Or Proposition(b)))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("![]a")
        self.assertEqual("(Not (Globally Proposition(a)))", str(ast))

    def test_parse_and(self):
        ast = parsing.parseLTL("phi & psi")
        self.assertEqual("(Proposition(phi) And Proposition(psi))", str(ast))
        
        # spacing is irrelevant
        ast = parsing.parseLTL("phi&psi")
        self.assertEqual("(Proposition(phi) And Proposition(psi))", str(ast))
        
        # can be chained (right associative)
        ast = parsing.parseLTL("phi&psi&chi")
        self.assertEqual("((Proposition(phi) And Proposition(psi)) And Proposition(chi))", str(ast))
        
        # space is irrelevant (even when chained)
        ast = parsing.parseLTL("phi & psi & chi")
        self.assertEqual("((Proposition(phi) And Proposition(psi)) And Proposition(chi))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("TRUE & FALSE")
        self.assertEqual("(Constant(TRUE) And Constant(FALSE))", str(ast))
        ast = parsing.parseLTL("TRUE & alpha")
        self.assertEqual("(Constant(TRUE) And Proposition(alpha))", str(ast))
        ast = parsing.parseLTL("alpha & FALSE")
        self.assertEqual("(Proposition(alpha) And Constant(FALSE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("(a | b) & x")
        self.assertEqual("((Proposition(a) Or Proposition(b)) And Proposition(x))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("[]a & <>b")
        self.assertEqual("((Globally Proposition(a)) And (Eventually Proposition(b)))", str(ast))
        ast = parsing.parseLTL("[]a & b")
        self.assertEqual("((Globally Proposition(a)) And Proposition(b))", str(ast))
        ast = parsing.parseLTL("a & <>b")
        self.assertEqual("(Proposition(a) And (Eventually Proposition(b)))", str(ast))
        
    def test_parse_or(self):
        ast = parsing.parseLTL("phi | psi")
        self.assertEqual("(Proposition(phi) Or Proposition(psi))", str(ast))
        # spacing is irrelevant
        ast = parsing.parseLTL("phi|psi")
        self.assertEqual("(Proposition(phi) Or Proposition(psi))", str(ast))
        # can be chained (left associative)
        ast = parsing.parseLTL("phi | psi | chi")
        self.assertEqual("((Proposition(phi) Or Proposition(psi)) Or Proposition(chi))", str(ast))
        # space is irrelevant (even when chained)
        ast = parsing.parseLTL("phi|psi|chi")
        self.assertEqual("((Proposition(phi) Or Proposition(psi)) Or Proposition(chi))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("TRUE | FALSE")
        self.assertEqual("(Constant(TRUE) Or Constant(FALSE))", str(ast))
        ast = parsing.parseLTL("TRUE | alpha")
        self.assertEqual("(Constant(TRUE) Or Proposition(alpha))", str(ast))
        ast = parsing.parseLTL("alpha | FALSE")
        self.assertEqual("(Proposition(alpha) Or Constant(FALSE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("(a | b) | x")
        self.assertEqual("((Proposition(a) Or Proposition(b)) Or Proposition(x))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("[]a | <>b")
        self.assertEqual("((Globally Proposition(a)) Or (Eventually Proposition(b)))", str(ast))
        ast = parsing.parseLTL("[]a | b")
        self.assertEqual("((Globally Proposition(a)) Or Proposition(b))", str(ast))
        ast = parsing.parseLTL("a | <>b")
        self.assertEqual("(Proposition(a) Or (Eventually Proposition(b)))", str(ast))
        
    def test_parse_xor(self):
        ast = parsing.parseLTL("phi ^ psi")
        self.assertEqual("(Proposition(phi) Xor Proposition(psi))", str(ast))
        # spacing is irrelevant
        ast = parsing.parseLTL("phi^psi")
        self.assertEqual("(Proposition(phi) Xor Proposition(psi))", str(ast))
        # can be chained (left associative)
        ast = parsing.parseLTL("phi ^ psi ^ chi")
        self.assertEqual("((Proposition(phi) Xor Proposition(psi)) Xor Proposition(chi))", str(ast))
        # space is irrelevant (even when chained)
        ast = parsing.parseLTL("phi^psi^chi")
        self.assertEqual("((Proposition(phi) Xor Proposition(psi)) Xor Proposition(chi))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("TRUE ^ FALSE")
        self.assertEqual("(Constant(TRUE) Xor Constant(FALSE))", str(ast))
        ast = parsing.parseLTL("TRUE ^ alpha")
        self.assertEqual("(Constant(TRUE) Xor Proposition(alpha))", str(ast))
        ast = parsing.parseLTL("alpha ^ FALSE")
        self.assertEqual("(Proposition(alpha) Xor Constant(FALSE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("(a ^ b) ^ x")
        self.assertEqual("((Proposition(a) Xor Proposition(b)) Xor Proposition(x))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("[]a ^ <>b")
        self.assertEqual("((Globally Proposition(a)) Xor (Eventually Proposition(b)))", str(ast))
        ast = parsing.parseLTL("[]a ^ b")
        self.assertEqual("((Globally Proposition(a)) Xor Proposition(b))", str(ast))
        ast = parsing.parseLTL("a ^ <>b")
        self.assertEqual("(Proposition(a) Xor (Eventually Proposition(b)))", str(ast))
        
    def test_parse_imply(self):
        ast = parsing.parseLTL("phi => psi")
        self.assertEqual("(Proposition(phi) Imply Proposition(psi))", str(ast))
        # spacing is irrelevant
        ast = parsing.parseLTL("phi=>psi")
        self.assertEqual("(Proposition(phi) Imply Proposition(psi))", str(ast))
        # can be chained (right associative)
        ast = parsing.parseLTL("phi => psi => chi")
        self.assertEqual("((Proposition(phi) Imply Proposition(psi)) Imply Proposition(chi))", str(ast))
        # space is irrelevant (even when chained)
        ast = parsing.parseLTL("phi=>psi=>chi")
        self.assertEqual("((Proposition(phi) Imply Proposition(psi)) Imply Proposition(chi))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("TRUE => FALSE")
        self.assertEqual("(Constant(TRUE) Imply Constant(FALSE))", str(ast))
        ast = parsing.parseLTL("TRUE => alpha")
        self.assertEqual("(Constant(TRUE) Imply Proposition(alpha))", str(ast))
        ast = parsing.parseLTL("alpha => FALSE")
        self.assertEqual("(Proposition(alpha) Imply Constant(FALSE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("(a | b) => x")
        self.assertEqual("((Proposition(a) Or Proposition(b)) Imply Proposition(x))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("[]a => <>b")
        self.assertEqual("((Globally Proposition(a)) Imply (Eventually Proposition(b)))", str(ast))
        ast = parsing.parseLTL("[]a => b")
        self.assertEqual("((Globally Proposition(a)) Imply Proposition(b))", str(ast))
        ast = parsing.parseLTL("a => <>b")
        self.assertEqual("(Proposition(a) Imply (Eventually Proposition(b)))", str(ast))
        
    def test_parse_iff(self):
        ast = parsing.parseLTL("phi <=> psi")
        self.assertEqual("(Proposition(phi) Equiv Proposition(psi))", str(ast))
        # spacing is irrelevant
        ast = parsing.parseLTL("phi<=>psi")
        self.assertEqual("(Proposition(phi) Equiv Proposition(psi))", str(ast))
        # can be chained (right associative)
        ast = parsing.parseLTL("phi <=> psi <=> chi")
        self.assertEqual("((Proposition(phi) Equiv Proposition(psi)) Equiv Proposition(chi))", str(ast))
        # space is irrelevant (even when chained)
        ast = parsing.parseLTL("phi<=>psi<=>chi")
        self.assertEqual("((Proposition(phi) Equiv Proposition(psi)) Equiv Proposition(chi))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("TRUE <=> FALSE")
        self.assertEqual("(Constant(TRUE) Equiv Constant(FALSE))", str(ast))
        ast = parsing.parseLTL("TRUE <=> alpha")
        self.assertEqual("(Constant(TRUE) Equiv Proposition(alpha))", str(ast))
        ast = parsing.parseLTL("alpha <=> FALSE")
        self.assertEqual("(Proposition(alpha) Equiv Constant(FALSE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("(a | b) <=> x")
        self.assertEqual("((Proposition(a) Or Proposition(b)) Equiv Proposition(x))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("[]a <=> <>b")
        self.assertEqual("((Globally Proposition(a)) Equiv (Eventually Proposition(b)))", str(ast))
        ast = parsing.parseLTL("[]a <=> b")
        self.assertEqual("((Globally Proposition(a)) Equiv Proposition(b))", str(ast))
        ast = parsing.parseLTL("a <=> <>b")
        self.assertEqual("(Proposition(a) Equiv (Eventually Proposition(b)))", str(ast))
        
    def test_parse_globally(self):
        ast = parsing.parseLTL("[] phi")
        self.assertEqual("(Globally Proposition(phi))", str(ast))
        
        # spacing is irrelevant
        ast = parsing.parseLTL("[]phi")
        self.assertEqual("(Globally Proposition(phi))", str(ast))
        
        # can be chained
        ast = parsing.parseLTL("[] [] [] phi")
        self.assertEqual("(Globally (Globally (Globally Proposition(phi))))", str(ast))
        
        # space is irrelevant (even when chained)
        ast = parsing.parseLTL("[][][]phi")
        self.assertEqual("(Globally (Globally (Globally Proposition(phi))))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("[]TRUE")
        self.assertEqual("(Globally Constant(TRUE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("[](a | b)")
        self.assertEqual("(Globally (Proposition(a) Or Proposition(b)))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("[]<>a")
        self.assertEqual("(Globally (Eventually Proposition(a)))", str(ast))
    
    def test_parse_eventually(self):
        ast = parsing.parseLTL("<> phi")
        self.assertEqual("(Eventually Proposition(phi))", str(ast))
        
        # spacing is irrelevant
        ast = parsing.parseLTL("<>phi")
        self.assertEqual("(Eventually Proposition(phi))", str(ast))
        
        # can be chained
        ast = parsing.parseLTL("<> <> <> phi")
        self.assertEqual("(Eventually (Eventually (Eventually Proposition(phi))))", str(ast))
        
        # space is irrelevant (even when chained)
        ast = parsing.parseLTL("<><><>phi")
        self.assertEqual("(Eventually (Eventually (Eventually Proposition(phi))))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("<>TRUE")
        self.assertEqual("(Eventually Constant(TRUE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("<>(a | b)")
        self.assertEqual("(Eventually (Proposition(a) Or Proposition(b)))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("<>[]a")
        self.assertEqual("(Eventually (Globally Proposition(a)))", str(ast))
        
    def test_parse_next(self):
        ast = parsing.parseLTL("() phi")
        self.assertEqual("(Next Proposition(phi))", str(ast))
        
        # spacing is irrelevant
        ast = parsing.parseLTL("()phi")
        self.assertEqual("(Next Proposition(phi))", str(ast))
        
        # can be chained
        ast = parsing.parseLTL("() () () phi")
        self.assertEqual("(Next (Next (Next Proposition(phi))))", str(ast))
        
        # space is irrelevant (even when chained)
        ast = parsing.parseLTL("()()()phi")
        self.assertEqual("(Next (Next (Next Proposition(phi))))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("()TRUE")
        self.assertEqual("(Next Constant(TRUE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("()(a | b)")
        self.assertEqual("(Next (Proposition(a) Or Proposition(b)))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("()[]a")
        self.assertEqual("(Next (Globally Proposition(a)))", str(ast))
        
    def test_parse_until(self):
        ast = parsing.parseLTL("phi U psi")
        self.assertEqual("(Proposition(phi) Until Proposition(psi))", str(ast))

        # operator name is case sensitive (cause parsing to end)
        ast = parsing.parseLTL("phi u psi")
        self.assertEqual("Proposition(phi)", str(ast))
        
        # spacing is relevant (U is a keyword, not a literal -> space imposed)
        ast = parsing.parseLTL("phiUpsi")
        self.assertEqual("Proposition(phiUpsi)", str(ast))
        # can be chained (right associative)
        ast = parsing.parseLTL("phi U psi U chi")
        self.assertEqual("((Proposition(phi) Until Proposition(psi)) Until Proposition(chi))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("TRUE U FALSE")
        self.assertEqual("(Constant(TRUE) Until Constant(FALSE))", str(ast))
        ast = parsing.parseLTL("TRUE U alpha")
        self.assertEqual("(Constant(TRUE) Until Proposition(alpha))", str(ast))
        ast = parsing.parseLTL("alpha U FALSE")
        self.assertEqual("(Proposition(alpha) Until Constant(FALSE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("(a | b) U x")
        self.assertEqual("((Proposition(a) Or Proposition(b)) Until Proposition(x))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("[]a U <>b")
        self.assertEqual("((Globally Proposition(a)) Until (Eventually Proposition(b)))", str(ast))
        ast = parsing.parseLTL("[]a U b")
        self.assertEqual("((Globally Proposition(a)) Until Proposition(b))", str(ast))
        ast = parsing.parseLTL("a U <>b")
        self.assertEqual("(Proposition(a) Until (Eventually Proposition(b)))", str(ast))
        
    def test_parse_weak_until(self):
        ast = parsing.parseLTL("phi W psi")
        self.assertEqual("(Proposition(phi) WeakUntil Proposition(psi))", str(ast))

        # operator name is case sensitive (cause parsing to end)
        ast = parsing.parseLTL("phi w psi")
        self.assertEqual("Proposition(phi)", str(ast))
        
        # spacing is relevant (U is a keyword, not a literal -> space imposed)
        ast = parsing.parseLTL("phiWpsi")
        self.assertEqual("Proposition(phiWpsi)", str(ast))
        # can be chained (right associative)
        ast = parsing.parseLTL("phi W psi W chi")
        self.assertEqual("((Proposition(phi) WeakUntil Proposition(psi)) WeakUntil Proposition(chi))", str(ast))
        
        # it may accept a constant
        ast = parsing.parseLTL("TRUE W FALSE")
        self.assertEqual("(Constant(TRUE) WeakUntil Constant(FALSE))", str(ast))
        ast = parsing.parseLTL("TRUE W alpha")
        self.assertEqual("(Constant(TRUE) WeakUntil Proposition(alpha))", str(ast))
        ast = parsing.parseLTL("alpha W FALSE")
        self.assertEqual("(Proposition(alpha) WeakUntil Constant(FALSE))", str(ast))
        
        # it may accept a parenthesized expression
        ast = parsing.parseLTL("(a | b) W x")
        self.assertEqual("((Proposition(a) Or Proposition(b)) WeakUntil Proposition(x))", str(ast))
                
        # it may accept a timed expression
        ast = parsing.parseLTL("[]a W <>b")
        self.assertEqual("((Globally Proposition(a)) WeakUntil (Eventually Proposition(b)))", str(ast))
        ast = parsing.parseLTL("[]a W b")
        self.assertEqual("((Globally Proposition(a)) WeakUntil Proposition(b))", str(ast))
        ast = parsing.parseLTL("a W <>b")
        self.assertEqual("(Proposition(a) WeakUntil (Eventually Proposition(b)))", str(ast))
        
    def test_parse_parenthesized(self):
        # no impact on vars
        ast = parsing.parseLTL("(a)")
        self.assertEqual("Proposition(a)", str(ast))
        
        # it permits to change the side-associativity
        # can be chained (right associative)
        ast = parsing.parseLTL("(phi | psi) | chi")
        self.assertEqual("((Proposition(phi) Or Proposition(psi)) Or Proposition(chi))", str(ast))
        
        ast = parsing.parseLTL("(phi & psi) & chi")
        self.assertEqual("((Proposition(phi) And Proposition(psi)) And Proposition(chi))", str(ast))
        
        ast = parsing.parseLTL("(phi => psi) => chi")
        self.assertEqual("((Proposition(phi) Imply Proposition(psi)) Imply Proposition(chi))", str(ast))
        
        ast = parsing.parseLTL("(phi <=> psi) <=> chi")
        self.assertEqual("((Proposition(phi) Equiv Proposition(psi)) Equiv Proposition(chi))", str(ast))
        
        ast = parsing.parseLTL("([]a) & b")
        self.assertEqual("((Globally Proposition(a)) And Proposition(b))", str(ast))
        
        ast = parsing.parseLTL("(<>a) & b")
        self.assertEqual("((Eventually Proposition(a)) And Proposition(b))", str(ast))
        
        ast = parsing.parseLTL("([]a) U (<>b)")
        self.assertEqual("((Globally Proposition(a)) Until (Eventually Proposition(b)))", str(ast))
        
        ast = parsing.parseLTL("([]a) W (<>b)")
        self.assertEqual("((Globally Proposition(a)) WeakUntil (Eventually Proposition(b)))", str(ast))
        
    def test_precedence(self):
        ast = parsing.parseLTL("!a U b)")
        self.assertEqual("((Not Proposition(a)) Until Proposition(b))", str(ast))
        