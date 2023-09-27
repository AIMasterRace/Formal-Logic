from copy import deepcopy
from proposition import *
from annotation import *


def inferable(premises, premise):
    for P in premises:
        if P == premise:
            return P

    if premise.op() == And:
        if ((P := inferable(premises, premise.P)) and (Q := inferable(premises, premise.Q))):
            return And(P, Q, AndI_A(P, Q))

    if premise.op() == Or:
        P = inferable(premises, premise.P)
        Q = inferable(premises, premise.Q)
        if (P or Q):
            return Or(P, Q, OrI_A(P or Q))

    if premise.op() == Implies:
        P = inferable(premises, Not(premise.P))
        Q = inferable(premises, premise.Q)
        if P or Q:
            return Implies(P, Q, OrI_A(P or Q))

    return None


def AndE(premises):
    k = set()
    for p in premises:
        if p.op() == And:
            k.add(p.P.construct(AndE_A(p)))
            k.add(p.Q.construct(AndE_A(p)))
    return k


def MP(premises):
    k = set()
    for p in premises:
        if p.op() == Implies and (C := inferable(premises, p.P)):
            k.add(p.Q.construct(MP_A(C, p)))
        elif p.op() == Or and (C := inferable(premises, Not(p.P))):
            k.add(p.Q.construct(MP_A(C, p)))
        elif p.op() == Or and (C := inferable(premises, Not(p.Q))):
            k.add(p.P.construct(MP_A(C, p)))

    return k


def MT(premises):
    k = set()
    for p in premises:
        if p.op() == Implies and (C := inferable(premises, Not(p.Q))):
            k.add(Not(p.P, MT_A(C, p)))
    return k


def Abs(premises):
    for P in premises:
        if (Q := inferable(premises, Not(P))):
            return {abs.construct(Abs_A(P, Q))}
    return set()


def DN(premises):
    k=set( )
    for P in premises:
        if P.op()== Not and P.P.op()==Not:
            k.add(P.P.P.construct(DN_A(P)))
    return k

abs = Atom("Absurdity")


class Scope:
    def __init__(self, premises):
        #print("Init")
        self.premises = premises

    def assume(self, assumption):
        return type(self)(self.premises.copy() | {assumption, })

    def __deduce(self):
        #print(self.premises)
        return AndE(self.premises) | MP(self.premises) | MT(self.premises) | Abs(self.premises) | self.OrE_deduce(self.premises) |DN(self.premises)

    def naive(self):
        '''Performs naive deduction based on the set of premises, returns new set of premises'''
        prems = self.premises.copy()
        while not (Ps := self.__deduce()).issubset(prems):
            #print(Ps)
            prems |= Ps
        return prems

    def RAA(self, assumption, RAAs, RAAleft):
        '''
        Creates new scope with assumption, tries to prove(Abs)
        Returns Not assumption or None
        '''
        #print(RAAs)
        #print(assumption)
        if (len(RAAs)<=0 or RAAleft <=0):
            return None
        S = self.assume(assumption)
        if (C := S.prove(abs, RAAs.difference({assumption, }), RAAleft-1)):
            print(Not(assumption))
            return Not(assumption, RAA_A(assumption, C))

    def CP_naive(self, assumption):
        '''Creates new scope with assumption, naive deduction, infer all new results'''
        # We do not use prove on CP to avoid infinite recursion
        # Justification is the fact all scopes bleed into the same scope regardless of the order of RAA or CP, hence we can assume RAA to be outside
        S = self.assume(assumption)
        ps = S.naive()
        return {Implies(assumption, P, CP_A(assumption, P)) for P in ps.difference({assumption} | self.premises)}

    def CP(self, assumption, SAAs, SAAsleft):
        print(SAAsleft)
        S = self.assume(assumption)
        S.premises= S.naive()
        if len(SAAs)<=0 or SAAsleft <= 0:
            return {Implies(assumption, P, CP_A(assumption, P)) for P in S.premises.difference(self.premises |  {assumption,})}
        k= set()
        for P in SAAs:
            k |= S.CP(P, SAAs.difference({P,}), SAAsleft-1)
            
        return {Implies(assumption, P, CP_A(assumption, P)) for P in k | S.premises.difference(self.premises |  {assumption,})}

    def OrE(self, assumption):
        '''Creates 2 new scopes with assumption, naive deduction on both,
          and because the inferences are only valuable if we can generate the same statement in both sets, we
          return the conjunction (Contradiction in one set implies we can get all the statements of the other)'''
        S1 = self.assume(assumption.P)
        S1.premises= S1.premises.difference({assumption, })
        S2 = self.assume(assumption.Q)
        S2.premises= S2.premises.difference({assumption, })
        ps1 = S1.naive().difference(self.premises)
        ps2 = S2.naive().difference(self.premises)

        k= set()

        if inferable(ps1, abs):
            ps1 |= ps2
        if inferable(ps2, abs):
            ps2 |= ps1

        for P in ps1:
            if (Q:=inferable(ps2, P)):
                k.add(P.construct(OrE_A(P, Q, assumption.P, assumption.Q)))
        print(k)
        return k
    
    def OrE_deduce(self, premises):
        k= set()
        for P in premises:
            if P.op()==Or:
                #print(premises)
                k|= self.OrE(P)
        return k

    def prove(self, consequent, RAAs=set(), RAAleft=1, SAAs= set(), SAAleft=1, tries=5):
        '''Returns annotated consequent or None'''
        # Proving algorithm uses naive deduction until it can't
        # VE, RAA and CP create a new scope in which we perform full naive deduction based on premises, and then analyse the returned consequents
        #print(RAAs)
        if (C := inferable(self.premises, consequent)):
            return C
        if not (C := self.naive()).issubset(self.premises):
            self.premises = C

        for P in SAAs:
            if (C:= self.CP(P, SAAs.difference({P,}), SAAleft-1)) and not C.issubset(self.premises):
                #print(C)
                self.premises |= C

        for P in RAAs:
            if (C:= self.RAA(P, RAAs.difference({P,}), RAAleft-1)) and not C.issubset(self.premises):
                #print(C)
                self.premises |= C
                
        

        if (tries <=0):
            return None
        return self.prove(consequent, RAAs, RAAleft, SAAs, SAAleft, tries-1)



pr= Prem_A()
P= Atom("P", pr)
Q= Atom("Q", pr)
R= Atom("R", pr)
T= Atom("T", pr)
S= Atom("S", pr)

test1= (set([And(P, Q, pr), Or(P,Q, pr), Implies(Or(P, R, pr), T, pr)]),
        And(And(P,Q,pr),T,pr))
test2= (set(),
        Implies(P,Implies(Q,And(P,Q,pr),pr),pr))
test3= (set((Not(R),Implies(P,R), Implies(Q,P))),
        Not(Q))
test4= ({Or(P,Q),},
        Not(And(Not(P),Not(Q))))

print(Scope(test4[0]).prove(test4[1],test4[1].conts(),1,test4[1].conts()))