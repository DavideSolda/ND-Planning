from pyddlib.bdd import BDD

class Omlette:

    def __init__(self, i):
        self.i = i

        #preparo le lettere proposizionali per gli stati
        self.num_eggs=[]
        for j in range(i+1):
            self.num_eggs.append(BDD.variable(j))

        self.bad      = BDD.variable(i+1)
        self.good     = BDD.variable(i+2)
        self.unbroken = BDD.variable(i+3)

        self.reg_nums = list(range(0, i+4))

        #preparo le lettere proposizionali per gli stati primed
        k=i+4
        self.num_eggs_primed=[]
        for j in range(i+1):
            self.num_eggs_primed.append(BDD.variable(k+j))

        self.bad_primed      = BDD.variable(k+i+1)#9
        self.good_primed     = BDD.variable(k+i+2)#10
        self.unbroken_primed = BDD.variable(k+i+3)#11

        self.primed_nums = list(range(k, k+i+4))

        #preparo le lettere proposizionali per le azioni
        self.prepareActions(k+i+4)

        self.act_nums = list(range(k+i+4, k+i+6))

        #preparo l'OBDD per Q
        self.Q =self.mutual_exclusion(self.num_eggs) & ((self.good & ~self.bad) | (~self.good & self.bad)) & self.ok0(self.num_eggs[0], self.bad, self.unbroken) & self.ok1(self.num_eggs[1], self.bad, self.unbroken)
        #self.Q = self.Q & self.ok0(self.num_eggs[0], self.bad, self.unbroken)#(~self.num_eggs[0] | (~self.bad & ~self.unbroken))
        """
        mutula exlusion tra numero di uova, tra bad e good e
        (
            #eggs=0->not bad & not unbroken
                |<<<<<-----&
            #eggs=1->not bad | not unbroken
        )
        """
        #preparo l'OBDD per Q'
        self.Q_primed = self.mutual_exclusion(self.num_eggs_primed) & self.mutual_exclusion([self.good_primed, self.bad_primed]) & (self.ok0(self.num_eggs_primed[0], self.bad_primed, self.unbroken_primed) & self.ok1(self.num_eggs_primed[1], self.bad_primed, self.unbroken_primed))

        #preparo l'OBDD per R
        self.prepareR()

    def prepareR(self):
        self.R= BDD.zero()

        #aggiungo BREAK
        #tranne per l'ultimo strato dove non lo posso applicare
        for j in range(self.i):
        #con unbroken non posso applicare break
        #se lo applico da bad  posso andare in bad  unbroken o bad
        #se lo applico da good posso andare in good unbroken o good
            self.R = self.R | (self.Q & self.num_eggs[j] & ~self.unbroken & self.good & self.actBreak & self.Q_primed & self.num_eggs_primed[j+1] & ~(self.bad_primed & self.unbroken_primed))
            """
            self.Q & self.num_eggs[j] & ~self.unbroken & self.good
                &
            self.actBreak
                &
            (self.Q_primed & self.num_eggs_primed[j+1] & ~(self.bad_primed & self.unbroken_primed))
            """
            self.R = self.R | (self.Q & self.num_eggs[j] & ~self.unbroken & self.bad & self.actBreak & self.Q_primed & self.num_eggs_primed[j+1] & self.bad_primed)
            """
            self.Q & self.num_eggs[j] & ~self.unbroken & self.bad
                &
            self.actBreak
                &
            self.Q_primed &  self.num_eggs_primed[j+1] & self.bad_primed
            """
        #aggiungo DISCARD
        #a tutti i nodi tranne al primo
        self.R = self.R | ((self.Q & ~self.num_eggs[0]) & self.actDiscard & (self.Q_primed & self.num_eggs_primed[0])) 

        #aggiungo open
        for j in range(1,self.i+1):
            """
            self.Q & self.num_eggs[j] & self.unbroken & self.bad
                &
            self.actOpen
                &
            self.Q_primed & self.num_eggs_primed[j] & ~self.unbroken_primed & self.bad_primed
            """
            self.R = self.R | (self.Q & self.num_eggs[j] & self.unbroken & self.bad) & self.actOpen & (self.Q_primed & self.num_eggs_primed[j] & ~self.unbroken_primed & self.bad_primed)
            """
            self.Q & self.num_eggs[j] & self.unbroken & self.good
                &
            self.actOpen
                &
            self.Q_primed & self.num_eggs_primed[j] & ~self.unbroken_primed
            """
            self.R = self.R | (self.Q & self.num_eggs[j] & self.unbroken & self.good) & self.actOpen & (self.Q_primed & self.num_eggs_primed[j] & ~self.unbroken_primed)

    def prepareActions(self, n):
        self.numAlpha0  = n
        self.numAlpha1  = n+1
        self.alpha0     = BDD.variable(n)
        self.alpha1     = BDD.variable(n+1)

        self.actBreak   = ~self.alpha0
        self.actOpen    = self.alpha0 & ~self.alpha1
        self.actDiscard = self.alpha0 & self.alpha1


    def mutual_exclusion(self, nm_eggs):
        me = BDD.zero()
        n = len(nm_eggs)
        for j in range(n):
            not_to_accept = [nm_eggs[l] for l in range(n) if l !=j]
            
            only_j = not_to_accept[0]
            for el in not_to_accept:
                only_j = only_j | el
            #print(~only_j)
            me= me | (~only_j & nm_eggs[j])

        return me
    def ok0(self, nmggs0, bd, nbrkn):
        return ~nmggs0 | (~bd & ~nbrkn)

    def ok1(self, nmggs1, bd, nbrkn):
        return ~nmggs1 | (~bd | ~nbrkn)

    def getInitialState(self):
        return self.num_eggs[0] & self.good & ~self.unbroken & self.Q

    def getFinalState(self):
        return self.num_eggs[self.i] & self.good & ~self.unbroken & self.Q

    def echoDot(self):
        f = open("graph.dot", "w")
        f.write("digraph D {\n")
        print("posizioni")
        print(self.reg_nums[:-3])
        print("bad good")
        print(self.reg_nums[-3:-1])
        print("posizioniPrimed")
        print(self.primed_nums[:-3])
        print("badPrimed goodPrimed")
        print(self.primed_nums[-3:-1])
        for i in self.reg_nums[:-3]:
            for j in self.reg_nums[-3:-1]:#solo per good e bad
                for k in self.primed_nums[:-3]:
                    for l in self.primed_nums[-3:-1]:#solo per good' e bad'

                        self.writeEdge(f,i,j,k,l,True,True)
                        self.writeEdge(f,i,j,k,l,True,False)
                        self.writeEdge(f,i,j,k,l,False,True)
                        self.writeEdge(f,i,j,k,l,False,False)

        f.write("}")
        f.close()
        import subprocess
        process = subprocess.Popen("dot -Tps graph.dot -o graph.ps".split(), stdout=subprocess.PIPE)
        output, error = process.communicate()
        process = subprocess.Popen("evince graph.ps".split(), stdout=subprocess.PIPE)
        output, error = process.communicate()


    def writeEdge(self,f,i,j,k,l,unbroken,unbrokenPrimed):
        state       = "bad" if self.i+1==j else "good"
        state       = state+"Unbroken" if unbroken else state
        numUnbroken = self.i+3
        stateP      = "bad" if 2*(self.i+1)+3==l else "good"
        stateP      = stateP+"Unbroken" if unbrokenPrimed else stateP
        numUnbrokenPrimed = 2*(self.i+1)+3+2


        dest=str(k-(self.i+1)-3)

        restriction=self.R.restrict({k:True, l:True, i:True, j:True, numUnbroken:unbroken, numUnbrokenPrimed:unbrokenPrimed})

        if restriction.restrict({self.numAlpha0:True, self.numAlpha1:True}) != BDD.zero():
            print(str(i)+"-*-"+str(j)+"|discard|"+str(k)+"-*-"+str(l)+"\t"+str(dest))
            f.write(state+str(i)+"->"+stateP+str(dest)+" [color=\"red\"];\n")
        if restriction.restrict({self.numAlpha0:False}) != BDD.zero():
            print(str(i)+"-*-"+str(j)+"|open|"+str(k)+"-*-"+str(l)+"\t"+str(dest))
            f.write(state+str(i)+"->"+stateP+str(dest)+" [color=\"orange\"];\n")
        if restriction.restrict({self.numAlpha0:True, self.numAlpha1:False}) != BDD.zero():
            print(str(i)+"-*-"+str(j)+"|break|"+str(k)+"-*-"+str(l)+"\t"+str(dest))
            f.write(state+str(i)+"->"+stateP+str(dest)+" [color=\"blue\"];\n")


if __name__ == "__main__":

    om=Omlette(1)
    om.echoDot()
    print(om.num_eggs[0] & om.Q & om.actDiscard & om.R & om.num_eggs_primed[0])# & om.actDiscard & om.R & om.num_eggs_primed[2] & om.good_primed & om.unbroken_primed)