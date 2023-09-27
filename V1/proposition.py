from abc import ABCMeta, abstractmethod
from annotation import *
class Proposition(metaclass=ABCMeta):
    @abstractmethod
    def eval(self):
        pass

    @abstractmethod
    def atoms(self):
        pass

    @abstractmethod
    def construct(self):
        pass

    @abstractmethod
    def infer(self):
        pass

    @abstractmethod
    def reduce(self):
        pass

    def op(self):
        return type(self)
    
    def flatten(self):
        return set((self,)) | self.annot.flatten()
    
    

class Monadic(Proposition):
    def __init__(self, P, annot):
        self.P=P
        self.annot=annot
    
    def __eq__(self, Q):
        return type(Q)==type(self) and self.P == Q.P
    
    def conts(self):    
        return self.P.conts() | set((self,))

    def construct(self, annot):
        return self.op()(self.P, annot)
    
    def __repr__(self):
        return f'({self.symbol} {str(self.P)})'
    
    def __hash__(self):
        return hash(str(self))
    
class Diadic(Proposition):
    def __init__(self, P, Q, annot):
        self.P=P
        self.Q=Q
        self.annot=annot
    
    def __eq__(self, Q):
        return type(Q)==type(self) and (self.P==Q.P and self.Q==Q.Q)
    def conts(self):    
        return self.P.conts() | self.Q.conts() | set((self,))
    
    def construct(self, annot):
        return self.op()(self.P, self.Q, annot)
    
    def __repr__(self):
        return f'({str(self.P)} {self.symbol} {str(self.Q)})'
    
    def __hash__(self):
        return hash(str(self))

class Atom(Proposition):
    def __init__(self, name, annot):
        self.name=name
        self.annot=annot

    def eval(self, **mapping):
        return mapping[self]
    
    def atoms(self):
        return set((self,))
    
    def conts(self):
        return set((self,))
    
    def construct(self, annot):
        return self.op()(self.name, annot)
    
    def __eq__(self, P):
        return self.op() == P.op() and self.name == P.name
    
    def __repr__(self):
        return self.name

    def __hash__(self):
        return hash(str(self))
    
    def reduce(self):
        return None
    
    def infer(self, premises):
        for p in premises:
            if p == self:
                return (set(), p)
        
        return None
        
        

class Not(Monadic):
    symbol= '~'
    def eval(self, **mapping):
        return not self.P.eval(**mapping)
    
    def atoms(self):
        return self.P.atoms()
    
    def reduce(self):
        return None
    
    def infer(self, premises):
        for p in premises:
            if p == self:
                return (set(),p)
        
        return None

class And(Diadic):
    symbol='&'
    def eval(self, **mapping):
        return self.P.eval(mapping) and self.Q.eval(mapping)
    
    def atoms(self):
        return self.P.atoms() | self.Q.atoms()
    
    def reduce(self):
        return None
    
    def infer(self, premises):
        for p in premises:
            if p == self:
                return (set(), p)
        if (pi := self.P.infer(premises)) and (qi := self.Q.infer(premises)):
            return (pi[0] | qi[0], self.construct(AndI_A(pi[1],qi[1])))
        
class Or(Diadic):
    symbol='|'
    def eval(self, **mapping):
        return self.P.eval(mapping) or self.Q.eval(mapping)
    
    def atoms(self):
        return self.P.atoms() | self.Q.atoms()
    
    def reduce(self):
        return None
    
    def infer(self, premises):
        for p in premises:
            if p == self:
                return (set(), p)
        pi = self.P.infer(premises)
        qi = self.Q.infer(premises)
        if pi:
            return (pi[0], self.construct(OrI_A(pi[1])),)
        if qi:
            return (qi[0], self.construct(OrI_A(qi[1])),)

    
class Implies(Diadic):
    symbol='->'
    def eval(self, **mapping):
        return (not self.P.eval(mapping)) or self.Q.eval(mapping)
    
    def atoms(self):
        return self.P.atoms() | self.Q.atoms()
    
    def reduce(self):
        return (self.Q, self.P.construct(Supp_A()))
    
    def infer(self, premises):
        for p in premises:
            if p == self:
                return (set(), p)
    #Theoretically Not P or Q but no actual inference rule for this so we must use E deduction

