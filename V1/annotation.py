from abc import ABCMeta,abstractmethod
class Annotate(metaclass=ABCMeta):
    @abstractmethod
    def __repr__(self):
        pass
    def op(self):
        return type(self)

class NullaryAnnot(Annotate):
    def __init__(self):
        super().__init__()

    def flatten(self):
        return set()
    
class MonadicAnnot(Annotate):
    def __init__(self,  P):
        super().__init__()
        self.P=P

    def flatten(self):
        return set((self.P,)) | self.P.flatten() 
    
class DyadicAnnot(Annotate):
    def __init__(self, P, Q):
        super().__init__()
        self.P=P
        self.Q=Q
    
    def flatten(self):
        return set((self.P,self.Q)) | self.P.flatten() | self.Q.flatten()
    
class TriadicAnnot(Annotate):
    def __init__(self, P, Q, R):
        super().__init__()
        self.P=P
        self.Q=Q
        self.R=R
    
    def flatten(self):
        return set((self.P,self.Q,self.R)) | self.P.flatten() | self.Q.flatten() | self.R.flatten()
    
class NadicAnnot(Annotate):
    def __init__(self, *args):
        super().__init__()
        self.props=args
    
    def flatten(self):
        s= set(self.props)
        for k in self.props:
            s |= k.flatten()
        return s
    
class Prem_A(NullaryAnnot):
    def __repr__(self):
        return "(Prem.)"

class Supp_A(NullaryAnnot):
    def __repr__(self):
        return "(Supp.)"

class Show_A(NullaryAnnot):
    def __repr__(self):
        return f"(Show.)"
    

class DN_A(MonadicAnnot):
    def __repr__(self):
        return f"(DN. {self.P})"

class AndE_A(MonadicAnnot):
    def __repr__(self):
        return f"(∧E. {self.P})"

class EFQ_A(MonadicAnnot):
    def __repr__(self):
        return f"(EFQ. {self.P})"

class OrI_A(MonadicAnnot):
    def __repr__(self):
        return f"(∨I. {self.P})"
    
class MP_A(DyadicAnnot):
    def __repr__(self):
        return f"(MP. {self.P}, {self.Q})"

class MT_A(DyadicAnnot):
    def __repr__(self):
        return f"(MT. {self.P}, {self.Q})"

class AndI_A(DyadicAnnot):
    def __repr__(self):
        return f"(∧I. {self.P}, {self.Q})"


class Abs_A(DyadicAnnot):
    def __repr__(self):
        return f"(Abs. {self.P}, {self.Q})"

class RAA_A(Annotate):
    def __init__(self, Supp, P, Premises):
        self.P= P
        self.Supp= Supp
        self.Premises= Premises

    def __repr__(self):
        return f"(RAA. {str(self.P)})"
    
    def flatten(self):
        s= set(self.Premises)
        for k in self.Premises:
            s |= k.flatten()
        return s 


class CP_A(Annotate):
    def __init__(self, Supp, P, Premises):
        self.P= P
        self.Supp= Supp
        self.Premises= Premises

    def __repr__(self):
        return f"(CP. {str(self.P)})"
    
    def flatten(self):
        s= set(self.Premises)
        for k in self.Premises:
            s |= k.flatten()
        return s 
    
class OrE_A(TriadicAnnot):
    def __repr__(self):
        return f"(∨I. {self.P}, {self.Q}, {self.R})"