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

    def op(self):
        return type(self)
    

class Monadic(Proposition):
    def __init__(self, P, annot= Prem_A()):
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
    def __init__(self, P, Q, annot= Prem_A()):
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
    def __init__(self, name, annot= Prem_A()):
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
    
        

class Not(Monadic):
    symbol= '~'
    def eval(self, **mapping):
        return not self.P.eval(**mapping)
    
    def atoms(self):
        return self.P.atoms()
    
class And(Diadic):
    symbol='&'
    def eval(self, **mapping):
        return self.P.eval(mapping) and self.Q.eval(mapping)
    
    def atoms(self):
        return self.P.atoms() | self.Q.atoms()

        
class Or(Diadic):
    symbol='|'
    def eval(self, **mapping):
        return self.P.eval(mapping) or self.Q.eval(mapping)
    
    def atoms(self):
        return self.P.atoms() | self.Q.atoms()
    
    
class Implies(Diadic):
    symbol='->'
    def eval(self, **mapping):
        return (not self.P.eval(mapping)) or self.Q.eval(mapping)
    
    def atoms(self):
        return self.P.atoms() | self.Q.atoms()
    

