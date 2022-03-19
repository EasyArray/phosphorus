from .phival import ConstantVal,PhiVal,LambdaVal,SpanVal
from .parse import Span

class NonBool(object): pass

class SemEntity(ConstantVal):
    def type(self): return "e"

def opcode(left, op, right):
    return SpanVal(str(left) + " " + op + " " + str(right) )
    
class SemLiteral(ConstantVal):
#    def __init__(self,s): self.s = s
#    def __repr__(self): return self.s
    def type(self): return "literal"
    def semtype(self):
        try:
            if self.stype:
                return self.stype
        except AttributeError: pass
        
        return ConstantVal("t")
    
    def __and__(self,other): 
        try:
            # If the other item is truly true, return self,
            # if truly false, return 0 
            return self if other else 0
        except:
            # if neither true/false, return the original code
            return opcode(self, "∧", other)

    def __rand__(self,other): 
        # Same as above, but opposite order
        try: 
            return self if other else 0
        except: 
            return opcode(other, "∧", self)

    def __or__(self,other):
        # For or it's 1 if the other is true
        try:
            return 1 if other else self
        except:
            return opcode(self, "∨", other)

    def __ror__(self,other): 
        # Other order
        try:
            return 1 if other else self
        except:
            return opcode(other, "∨", self)

    def __invert__(self): return SpanVal("¬" + self)

    # NOTE: a little dangerous, since we basically can't compare SemLiterals
    def __eq__(self,other):
        return opcode(self, "==", other)

    # Since SemLiterals do not have a known value, we don't want them
    # short-circuiting boolean "and" and "or" in python. 
    # We use & and | instead
    def __bool__(self): raise NotImplementedError
    
class SemPred(ConstantVal):
    def type(self): return "predicate"
    def __call__(self, *args):
        print("SemPred call")
        return SemLiteral("{}({})".format(repr(self),*args))

class SemVar(ConstantVal):
    def __new__(cls, s, t=None):
        try:    (s, typ) = s.split("_")
        except: typ = t
        
        self = ConstantVal.__new__(cls,s)
        self.typ = typ
        return self
    
    def is_variable(self,_variables=[]): return True
    
    def match(self, target, _variables=[]):
        print("SemVar match", self, target, variables)
        if self.type()==target.type():
            return {self:target}
        else: return None
    
    def type(self):
        return "variable"
    
    def semtype(self):
        return self.typ
        
    def __repr__(self):
        if self.typ: return self + "∈" + str(self.typ)
        return self
        
    __str__ = __repr__