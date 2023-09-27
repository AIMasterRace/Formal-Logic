from abc import ABCMeta, abstractmethod
from sys import setrecursionlimit

setrecursionlimit(1200)
class Proof:
    #A valid proof must be treated as its consequent
    def __init__(self, premises, supposition, consequent):
        self.premises= premises
        self.supposition= supposition
        self.consequent= consequent
        self.propositions=[]
    def __repr__(self):
        return f'{self.premises} ⊤ {self.consequent}'

from proposition import *
from annotation import *
#TBD
#Proof class, premises, aimed conclusion
#Deduce function, details all the relationships
#Contradiction array, all possible contradictions
#inferable returns a tuple of the set of annotated propositions needed to construct the given consequent and the final consequent

Abs= Atom("Absurdity", Prem_A())

def AndE(premises):
    k= set()
    i=1
    for p in premises:
        if p.op() == And:
            k.add(p.P.construct(AndE_A(p))) 
            k.add(p.Q.construct(AndE_A(p)))
    return k

def MP(premises):
    k= set()
    for p in premises:
        if p.op() == Implies and (C:=inferable(premises, p.P)):
            k.add(p.Q.construct(MP_A(C[1], p)))
            k.union(C[0])
        elif p.op() == Or and (C:=inferable(premises,Not(p.P,pr))):
            k.add(p.Q.construct(MP_A(C[1], p)))
            k.union(C[0])
    return k

def MT(premises):
    k= set()
    for p in premises:
        if p.op() == Implies and (C:=inferable(premises, Not(p.Q,Prem_A()))):
            k.add(Not(p.P, MT_A(C[1], p)))
            k.union(C[0])
        elif p.op() == Or and (C:=inferable(premises,Not(p.Q,pr))):
            k.add(Not(p.P, MT_A(C[1], p)))
            k.union(C[0])
    return k    

def RAA(premises):
    k=set()
    for P in premises:
        if (Q:=inferable(premises, Not(P,pr), False)):
            #print("HerE")
            k.add(Abs.construct(Abs_A(P,Q[1])))
    return k
#Strong elimination is quite hard to implement
#We use weak elimination and strong MP, MT, and Supp.

def OrE(premises):
    for P in premises:
        for Q in premises:
            if P.op()==Or and Q.op() == Implies and P.P==Q.P and (C:=inferable(premises, Implies(P.Q,Q.Q,pr))):
                #print("HerE")
                return C[0] | {Q.Q.construct(OrE_A(P,Q,C[1])),}
    return set()
            

def DN(premises):
    k= set()
    for p in premises:
        if (p.op()==Not and p.P.op()== Not):
            k.add(p.P.P)
    return k
#Contradiction represents scope change hence will be implemented in prove

def EFQ(premises, consequent):
    if (C:=inferable(premises, Abs)):
        return set((consequent.construct(EFQ_A(C[0])),))
    return None

def CP(premises, assumption, consequent, RAAs=None, RAAleft=0):
    k=set() #Add    assumption -> consequent, Annot CP is the flattened final consequent
    if (C:=prove(premises | set((assumption,)), consequent,RAAs, RAAleft))[1]:
        k.add(Implies(assumption, consequent, CP_A(assumption.construct(Supp_A()), C[1], premises.copy())))
    return k

def Supp(premises, assumption, RAAs=None, RAAleft=1):
    proof= prove(added(premises, assumption), Abs, RAAs, RAAleft)
    k=set()
    if proof[1] is not None and proof[1]==Abs:
        k.add(Not(assumption.construct(Supp_A()), RAA_A(assumption.construct(Supp_A()),proof[1], premises.copy())))
    else:
        for P in proof[0].difference(premises):
            if assumption==P:
                continue
            #print(assumption, assumption.annot, P, P.annot)
            k.add(Implies(assumption.construct(Supp_A()),P, CP_A(assumption.construct(Supp_A()),P,premises.copy()))) 
    return k 
def deduce(premises):
    '''
    Given a set of premises Pi, we aim to deduce all that can be deduced in 1 step given the inference rules.
    '''
    return AndE(premises) | MP(premises) | MT(premises) | RAA(premises) | OrE(premises) | DN(premises)

def inferable(premises, consequent, deduce=False):
    '''
    Given a set of premises Pi, we aim to construct the consequent using the I rules \n
    Returns (Steps, Annotated Consequent) or None    
    '''
    if deduce:
        return consequent.infer(premises)  or prove(premises, consequent, RAAleft=0)
    return consequent.infer(premises)

def reducable(consequent):
    '''Returns (new consequent, steps) or None'''
    return consequent.reduce()

def added(s, p):
    return s | set((p,))
def prove(premises, consequent, RAAs=None, RAAleft=1):
    '''Returns (proven premises, final consequent) or None'''
    if not RAAs:
        RAAs= consequent.conts()
        RAAs= RAAs | set(map(lambda x: Not(x,pr), RAAs))

    if (C:=inferable(premises, consequent, deduce=False)):
        return (premises|C[0], C[1])
    if (C:=reducable(consequent)):
        return prove(premises | CP(premises, C[1], C[0]), consequent, RAAs, RAAleft)

    if not deduce(premises).issubset(premises):
        #print(deduce(premises).difference(premises))
        return prove(premises | deduce(premises), consequent, RAAs, RAAleft)
    
    if RAAleft > 0:
        #print("Supp called")
        #print(len(premises))
        for RA in RAAs:
            if (C:=Supp(premises,RA,RAAs.difference(set((RA,))),RAAleft-1)) != set():
                #print(premises)
                return prove(premises | C,consequent,RAAs.difference(set((RA,))),RAAleft)
    
    return (premises, None)
def flatten(premise):
    return premise.flatten()

def construct_proof(premises, result):
    s= flatten(result)
    ls=list(premises)
    while len(s) > len(premises):
        for i in s:
            #if i.op() in (Implies, Or) and i.P==i.Q:
            #    premises.add(i)
            #    continue
            if i.annot.op() in (CP_A,RAA_A) and (i.annot.Premises).issubset(premises) and i not in premises:
                ls.append(list(filter(lambda k: type(k) is list or k not in premises, construct_proof(premises | set((i.annot.Supp,)), i.annot.P))))
                ls.append(i)
                premises.add(i)
            elif i.annot.op() != CP_A and i.annot.flatten().difference({i,}).issubset(premises) and i not in premises:
                ls.append(i)
                premises.add(i)
        
    return ls

def to_string(proof):
    ls=[]
    for i in proof:
        if type(i)== list:
            ls += list(map(lambda k: ' '*4  +k, to_string(i)))
        else:
            ls.append(f'{i} {i.annot}')
    return ls

def natural_deduction(premises, consequent, RAAs=None, RAAleft=3):
    print("Prove. ", premises, ' -> ', consequent)
    result=prove(premises, consequent, RAAs, RAAleft)[1]
    print(flatten(result), result.annot)
    proof= construct_proof(premises, result)
    for i in to_string(proof):
        print(i)
    



pr= Prem_A()
P= Atom("P", pr)
Q= Atom("Q", pr)
R= Atom("R", pr)
T= Atom("T", pr)
S= Atom("S", pr)

#test1= (set([And(P, Q, pr), Or(P,Q, pr), Implies(Or(P, R, pr), T, pr)]),
#        And(And(P,Q,pr),T,pr))
#test2= (set(),
#        Implies(P,Implies(Q,And(P,Q,pr),pr),pr))
#test3= (set((Not(R),Implies(P,R), Implies(Q,P))),
#        Not(Q))
test4= (set(),
        Or(Not(Implies(And(P,Q,pr),R,pr),pr),Implies(And(P,Q,pr),R,pr),pr))

#natural_deduction(*test1)
print()
#natural_deduction(*test2)
print()
#natural_deduction(*test3)
print()
natural_deduction(*test4)




