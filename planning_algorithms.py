from pyddlib.bdd import BDD
import time
from omlette import *

class Planning_algo:
    #in a, p, p_primed set di identificativi delle variabili
    def __init__(self, ist):
        self.p=ist.reg_nums
        self.p_primed=ist.primed_nums
        self.a=ist.act_nums
        self.R=ist.R
        self.Q=ist.Q
        self.Q_primed=ist.Q_primed

    def weakPlan(self, i, g):

        oldSA=BDD.zero()
        sA=BDD.zero()
        c=1
        while True:
            print(c)
            c=c+1
            preImage = self.weakPreImage(self.fromReg2Primed(g | self.statesOf(sA)))

            newSA    = self.pruneStates(preImage, g | self.statesOf(sA))

            oldSA    = sA
            sA       = sA | newSA

            if oldSA == sA:
                break
            if (~i | (g | self.statesOf(sA))) == BDD.one():
                break
        return sA if(~i | (g | self.statesOf(sA))) == BDD.one() else BDD.zero()

    def weakPlan(self, i, g):

        oldSA=BDD.zero()
        sA=BDD.zero()
        c=1
        while True:
            print(c)
            c=c+1
            preImage = self.weakPreImage(self.fromReg2Primed(g | self.statesOf(sA)))
            #print(self.statesOf(preImage))
            newSA    = self.pruneStates(preImage, g | self.statesOf(sA))

            oldSA    = sA
            sA       = sA | newSA

            if oldSA == sA:
                break
                print("here1")
            if (~i | (g | self.statesOf(sA))) == BDD.one():
                print("here2")
                break
        return sA if(~i | (g | self.statesOf(sA))) == BDD.one() else BDD.zero()

    def strongPlan(self, i, g):

        oldSA=BDD.zero()
        sA=BDD.zero()
        c=1
        while True:
            print(c)
            c=c+1
            preImage = self.strongPreImage(self.fromReg2Primed(g | self.statesOf(sA)))
            #print(self.statesOf(preImage))
            newSA    = self.pruneStates(preImage, g | self.statesOf(sA))

            oldSA    = sA
            sA       = sA | newSA

            if oldSA == sA:
                break
                print("here1")
            if (~i | (g | self.statesOf(sA))) == BDD.one():
                print("here2")
                break
        return sA if(~i | (g | self.statesOf(sA))) == BDD.one() else BDD.zero()

    def fromReg2Primed(self, obdd):
        #print(obdd)
        obddPrimed = obdd

        for j in self.p:
            x          = BDD.variable(j)
            xP         = BDD.variable(self.p_primed[j])
            obddPrimed = obddPrimed & ~(x^xP) #negazione dello xor

        for j in self.p:

            obddPrimed = (obddPrimed.restrict({j:True}) | obddPrimed.restrict({j:False}))

        if obddPrimed & self.Q_primed != obddPrimed:
            print("fromReg2Primed fuori da Q_primed")
        #print(obddPrimed)
        return obddPrimed

    def existentialClousure(self, obdd, vars):
        """
        if len(vars)>=1:
            obddVT=self.existentialClousure(obdd.restrict({vars[0]:True}),  vars[1:])
            obddVF=self.existentialClousure(obdd.restrict({vars[0]:False}), vars[1:])
            obdd = obddVT | obddVF
        """
        for i in vars:
            obddVT=obdd.restrict({i:True})
            obddVF=obdd.restrict({i:False})
            obdd = obddVT | obddVF
        return obdd

    def statesOf(self, sA):
        return self.existentialClousure(sA, self.a+self.p_primed)

    def weakPreImage(self, sP):

        wp = self.R & sP

        if not (~wp | self.R):
            print("errore in wp = self.R & sP")

        wp = self.existentialClousure(wp, self.p_primed)

        if not (~self.statesOf(wp) | self.Q):
            print("stati fuori Q in wp")

        return wp

    def strongPreImage(self, sP):

        wp = self.R & sP

        wpNoGood = self.R & ~sP

        wp = wp & ~wpNoGood

        if not (~wp | self.R):
            print("errore in wp = self.R & sP")

        wp = self.existentialClousure(wp, self.p_primed)

        if not (~self.statesOf(wp) | self.Q):
            print("stati fuori Q in wp")

        return wp

    def pruneStates(self, sA, q):
        #print(self.statesOf(sA))
        if not (sA & ~q & ~self.R)!=BDD.zero():
            print("not (sA & ~q & ~self.R)!=BDD.zero())")

        return sA & ~q

    def echoPlan(self, sA):
        print("State Action Table")
        for i in self.p[:-3]:
            for j in self.p[-3:]:
                if sA.restrict({i:True, j:True, 12:True, 13:True}) != BDD.zero():
                    print("|"+str(i)+"--"+str(j)+"--"+"|"+"Disc")
                if sA.restrict({i:True, j:True, 12:False}) != BDD.zero():
                    print("|"+str(i)+"--"+str(j)+"--"+"|"+"Open")
                if sA.restrict({i:True, j:True, 12:True, 13:False}) != BDD.zero():
                    print("|"+str(i)+"--"+str(j)+"--"+"|"+"Break")


if __name__ == "__main__":

    om=Omlette(2)

    planner = Planning_algo(om)
    
    startTime = time.time()
    wPlan=planner.weakPlan(om.getInitialState(), om.getFinalState())
    sPlan=planner.strongPlan(om.getInitialState(), om.getFinalState())
    planner.echoPlan(sPlan)
    print(sPlan)
    print(time.time()-startTime)
#    print(wPlan)
