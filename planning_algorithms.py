from pyddlib.bdd import BDD
from omlette import *

class Planning_algo:
    #in a, p, p_primed set di identificativi delle variabili
    def __init__(self, ist, n):
        self.p=ist.reg_nums
        self.p_primed=ist.primed_nums
        self.a=ist.act_nums
        self.r=ist.R
        self.n=n
        self.Q=ist.Q
        self.Q_primed=ist.Q_primed

    def weakPlan(self, i, g):

        oldSA=BDD.zero()
        sA=BDD.zero()
        while True:
            preImage = self.weakPreImage(self.fromReg2Primed(g | self.statesOf(sA)))
            print(self.statesOf(preImage))
            newSA    = self.pruneStates(preImage, g | self.statesOf(sA))
            #print(self.statesOf(newSA))
            oldSA    = sA
            sA       = sA | newSA
            test     = BDD.zero() if (oldSA == sA) else BDD.one()
            if (test & (~i | (g | self.statesOf(sA)))):
                break
        return sA if(~i | (g | self.statesOf(sA))) else BDD.zero()

    def fromReg2Primed(self, obdd):
        #print(obdd)
        obddPrimed = obdd

        for j in self.p:
            x          = BDD.variable(j)
            xP         = BDD.variable(self.p_primed[j])
            obddPrimed = obddPrimed & ~(x^xP) #negazione dello xor
        """
        for j in self.p:
            # sse per ciascuna variabile
            xP         = BDD.variable(self.p_primed[j])
            obddUpdate = (obdd.restrict({j:True}) | ~xP) & (obdd.restrict({j:False}) | xP)
            obddPrimed = obddPrimed | (obddUpdate.restrict({j:True}) | obddUpdate.restrict({j:False}))
        """
        for j in self.p:

            obddPrimed = (obddPrimed.restrict({j:True}) | obddPrimed.restrict({j:False}))
        
        #print(obddPrimed)
        return obddPrimed

    def statesOf(self, sA):
        s=sA
        for x in self.a:
            s = s.restrict({x:True}) | s.restrict({x:False})
        for x in self.p_primed:
            s = s.restrict({x:True}) | s.restrict({x:False})
        return s

    def weakPreImage(self, sP):

        wp = self.r & sP
        
        for x in self.p_primed:
            wp = wp.restrict({x:True}) | wp.restrict({x:False})

        return wp

    def pruneStates(self, sA, q):
        #print(self.statesOf(sA))
        return sA & ~q

if __name__ == "__main__":

    om=Omlette(2)

    planner = Planning_algo(om, 2)

    wPlan=planner.weakPlan(om.getInitialState(), om.getFinalState())
    print(wPlan)