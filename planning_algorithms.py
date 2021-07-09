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
            self.echoPlan(newSA)
            oldSA    = sA
            sA       = sA | newSA

            if oldSA == sA:
                break
            if (~i | (g | self.statesOf(sA))) == BDD.one():
                break
        return sA if(~i | (g | self.statesOf(sA))) == BDD.one() else BDD.zero()

    def strongPlan(self, i, g):

        oldSA=BDD.zero()
        sA=BDD.zero()
        c=1
        while True:

            preImage = self.strongPreImage(self.fromReg2Primed(g | self.statesOf(sA)))
            newSA    = self.pruneStates(preImage, g | self.statesOf(sA))
            print(c)
            c=c+1
            self.echoPlan(newSA)
            oldSA    = sA
            sA       = sA | newSA
            if oldSA == sA:
                break
                print("here1")
            if (~i | (g | self.statesOf(sA))) == BDD.one():
                print("here2")
                break
        return sA if(~i | (g | self.statesOf(sA))) == BDD.one() else BDD.zero()

    def strongCyclicPlan(self, i, g):
        univSA = self.existentialClousure(self.R & ~g, self.p_primed)
        oldSA  = BDD.zero()
        sA     = univSA
        c      = 1
        while True:
            print(c)
            c=c+1
            oldSA = sA
            #print("self.pruneOutgoing(sA,g)")
            #self.echoPlan(self.pruneOutgoing(sA,g))
            sA    = self.pruneUnconnected(self.pruneOutgoing(sA,g),g)
            #print("self.pruneUnconnected(self.pruneOutgoing(sA,g),g)")
            #self.echoPlan(sA)
            #print("oldSA == sA")
            #print(oldSA == sA)
            if oldSA == sA:
                break
        if (univSA==sA):#vale solo per le omlette
            print("No errori sino a qui")
        else:
            print("Errori nel loop")
        ok = (~i | (g | self.statesOf(sA))) == BDD.one()
        return self.removeNonProgess(sA,g) if ok else BDD.zero()

    def removeNonProgess(self, sA, g):

        newSA = BDD.zero()
        c     = 1
        while True:
            print(c)
            c = c+1
            preImage = sA & self.weakPreImage(self.fromReg2Primed(g | self.statesOf(newSA)))
            oldSA    = newSA
            newSA    = newSA | self.pruneStates(preImage, g | self.statesOf(newSA))
            print("actual newSA")
            self.echoPlan(newSA)
            if (oldSA == newSA):
                return newSA

    def pruneUnconnected(self, sA, g):

        newSA = BDD.zero()
        c     = 1
#        print("loop in pruneUnconnected")
        while True:

            oldSA = newSA
            #self.echoPlan(self.weakPreImage(self.fromReg2Primed(g | self.statesOf(newSA))))
            newSA  = sA & self.weakPreImage(self.fromReg2Primed(g | self.statesOf(newSA)))

            
            if oldSA == newSA:
                return newSA

    def pruneOutgoing(self, sA, g):
        #SA\computeOutgoing(SA, G U StatesOf(SA))
        #print("sA & ~(self.computeOutgoing(sA, g | self.statesOf(sA)))==sA")
        #print(sA & ~(self.computeOutgoing(sA, g | self.statesOf(sA)))==sA)
        return sA & ~(self.computeOutgoing(sA, g | self.statesOf(sA)))

    def computeOutgoing(self, sA, S):
        #print("computeOutgoing")
        #print(self.existentialClousure(self.R & ~self.fromReg2Primed(S), self.p_primed))
#        self.echoPlan(self.existentialClousure(self.R & ~self.fromReg2Primed(S), self.p_primed))
        return self.existentialClousure(self.R & ~self.fromReg2Primed(S), self.p_primed)

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

        for i in vars:
            obdd = obdd.restrict({i:True}) | obdd.restrict({i:False})
        return obdd

    def universalClousure(self, obdd, vars):

        for i in vars:
            obdd = obdd.restrict({i:True}) & obdd.restrict({i:False})
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
        #{(s,a):Exec(s,a)subseteq S}
        #for all x' (R(x,alpha,x') --> Q(x')) AND applicable(x,alpha)
        applicable = self.existentialClousure(self.R, self.p_primed)

        return self.universalClousure((~self.R | sP), self.p_primed) & applicable

    def pruneStates(self, sA, q):
        #print(self.statesOf(sA))
        if not (sA & ~q & ~self.R)!=BDD.zero():
            print("not (sA & ~q & ~self.R)!=BDD.zero())")

        return sA & ~q

    def echoPlan(self, sA):
        print("State Action Table")
        numMaxEggs  = len(self.p[:-3])-1
        print("numMaxEggs: "+str(numMaxEggs))
        for i in self.p[:-3]:
            for j in self.p[-3:-1]:

                state       = "bad" if j==self.p[-3] else "good"
                unbrokenPos = self.p[-1]
                alpha0      = unbrokenPos+1+numMaxEggs+4
                alpha1      = alpha0+1
                #caso non unbroken
                restriction = sA.restrict({i:True, j:True})
                if restriction.restrict({unbrokenPos:False, alpha0:True, alpha1:True}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"\t\t|"+"Disc")
                if restriction.restrict({unbrokenPos:False, alpha0:False}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"\t\t|"+"Break")
                if restriction.restrict({unbrokenPos:False, alpha0:True, alpha1:False}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"\t\t|"+"Open")
                #caso unbroken
                if restriction.restrict({unbrokenPos:True, alpha0:True, alpha1:True}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"Unbroken"+"\t|"+"Disc")
                if restriction.restrict({unbrokenPos:True, alpha0:False}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"Unbroken"+"\t|"+"Break")
                if restriction.restrict({unbrokenPos:True, alpha0:True, alpha1:False}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"Unbroken"+"\t|"+"Open")

if __name__ == "__main__":

    om=Omlette(1)

    planner = Planning_algo(om)
    
    startTime = time.time()
    #wPlan=planner.weakPlan(om.getInitialState(), om.getFinalState())
    #sPlan=planner.strongPlan(om.getInitialState(), om.getFinalState())
    #planner.echoPlan(sPlan)
    #print(wPlan)
    sCPlan=planner.strongCyclicPlan(om.getInitialState(), om.getFinalState())
    #print(sCPlan)
    print("final plan")
    planner.echoPlan(sCPlan)
    print(time.time()-startTime)
#    print(wPlan)

"""
    def echoPlan(self, sA):
        print("State Action Table")
        for i in self.p[:-3]:
            for j in self.p[-3:-1]:
                numMaxEggs  = len(self.p[:-3])-1
                state       = "bad" if j==self.p[-3] else "good"
                numUnbroken = numMaxEggs+3
                alpha0      = self.p[-2]
                alpha1      = self.p[-1]
                #caso non unbroken
                if sA.restrict({i:True, j:True, numUnbroken:False, alpha0:True, alpha1:True}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"\t\t|"+"Disc")
                if sA.restrict({i:True, j:True, numUnbroken:False, alpha0:False}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"\t\t|"+"Break")
                if sA.restrict({i:True, j:True, numUnbroken:False, alpha0:True, alpha1:False}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"\t\t|"+"Open")
                #caso unbroken
                if sA.restrict({i:True, j:True, numUnbroken:True, alpha0:True, alpha1:True}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"Unbroken"+"\t|"+"Disc")
                if sA.restrict({i:True, j:True, numUnbroken:True, alpha0:False}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"Unbroken"+"\t|"+"Break")
                if sA.restrict({i:True, j:True, numUnbroken:True, alpha0:True, alpha1:False}) != BDD.zero():
                    print("| at "+str(i)+" "+state+"Unbroken"+"\t|"+"Open")
"""