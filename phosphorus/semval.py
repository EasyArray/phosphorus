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
    
    def __and__(self,other): return opcode(self, "∧", other)
    def __rand__(self,other): return opcode(other, "∧", self)
    def __or__(self,other): return opcode(self, "∨", other)
    def __ror__(self,other): return opcode(other, "∨", self)
    def __invert__(self): return SpanVal("¬" + self)

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