import itertools

class Fact:
 
    #depth is the number of nested cases in which the fact has been shown
    def __init__(self, name, args, dependencies = [], label = None, disAncestors = []):
        self.name = name
        self.args = args
        self.dependencies = dependencies #the facts needed to conclude this fact, list of fact labels
        
        self.disAncestors = set() #set of disjunction facts needed to conclude this fact (anywhere in ancestry)
                                  #each entry is of the form (DisjunctionLabel, disjunctionIndex)
        
        self.concThm = None #the theorem that was used to conclude this Fact
        self.label = label
 
    def doPrint(self):
        print(self.label, " : ", self.name, " ", self.args, " :: ", self.dependencies, " :: " , self.disAncestors)
 
    def equals(self,fact):
        if self.name != fact.name: return False
        if self.args != fact.args: return False
        return True
 
    def copy(self):
        return Fact(self.name, list(self.args), self.depth)
 
    #returns a normal form for the fact structure
    #useful for matching facts to theorem arguments
    #the structure of a fact is uniquely specified by the name and number of arguments
    #TEST THIS!!!
 #   def normal_form(self):
         
#        return self.name + str(len(args))
         
 
#an OR of facts
class Disjunction:
    
    def __init__(self, facts, dependencies = [], label = None, disAncestors = []):
        self.facts = facts
        self.dependencies = dependencies
        self.disAncestors = set()
        self.label = label
    
    def doPrint(self):
        facts = self.facts
        print(self.label, ":")
        for i in range(0,len(facts)):
            facts[i].doPrint()
            if(i != len(facts) - 1):
                print("    OR")
         
 
#theorem specified by:
# list of placeholders
# list of facts using placeholders
# list of conclusions using placeholders
 
#for example: 
# symbols:     G, H, I
# facts:       subgroup H G, subgroup I H
# conclusions: subgroup I G
 
class Theorem:
 
    #a theorem should 
    def __init__(self, facts, conclusions, name):
        self.facts = facts
        self.conclusions = conclusions
        self.name = name
 
class HyperTheorem:
 
    #rule is a function that takes in series of facts with structure 'facts' and ouputs a list of facts
    def __init__(self, facts, rule, name):
        self.facts = facts
        self.rule = rule
        self.name = name
        self.multiArgs = False #can the theorem take multiple arguments?
 
class ProofEnvironment:
 
    #begin with a list of facts
    #list of facts grows as theorems are applied
    #theorems is the set of theorems in the environment
    #theorem_names_dict is a dictionary of theorem names
    #goal is the fact to be proven
    def __init__(self, facts, theorems, theorem_name_dict, goal):
        self.facts = []
        self.theorems = theorems
        self.theorem_name_dict = theorem_name_dict
        self.disjunctions = []
        
        self.goal = goal
        self.goalAchieved = False #goal should not already be achieved (probably should check it though)
        self.goalDisCombos = []
 #       self.goalLabel = None
 
 #       self.caseDepth = 0
 
        #factLabels maps labels to facts
        #makes it easier to refer to a specific fact
        self.factLabels = {}
        self.curFactNum = 0
 
        #the set of additional assumptions describing the current state of the environment
        #a new assumption is added whenever case is called

 
        self.addNewFacts(facts)
        self.symbolSet = set() #the set of all symbols currently in the environment


        #TEST TEST
 #       print("Second Test")
#        for fact in facts: #TEST
#            fact.doPrint()
#            print(type(fact))
#            print()
        
        for fact in self.facts:
            for sym in fact.args:
                self.symbolSet.add(sym)

    def newLabel(self, letter = 'F'):
        label = letter + str(self.curFactNum)
        self.curFactNum += 1
        return label

    #has the goal been achieved yet
    #goalFact is a new copy of goal used for the update
    def updateGoalAchieved(self, goalFact):
        disLabels = set([D for D,i in goalFact.disAncestors]) #prevent duplicates
#        disFacts = [ f.lbl for f in [self.factLabels[D].facts for D in disLabels] ] #the list of fact label lists corresponding to each disjunction
        L = [(D,len(self.factLabels[D].facts)) for D in disLabels]
        #S = set() #list of all tuples of facts ( in the form (D,7) ) that need to exist
        X = []
        for D, l in L:
            X.append([(D,i) for i in range(0,l)])
        S = list(itertools.product(*X))
#        print("S :: ", S)
        S = set(frozenset(u) for u in S)

#        print("goalDisCombos: ", self.goalDisCombos)
 #       print("S: ", S)

        frozenDisCombos = set(frozenset(d) for d in self.goalDisCombos)
        if frozenDisCombos.issuperset(S): #SET UP SO NO CASTING
            self.goalAchieved = True
        
 
    def addNewFacts(self,newFacts):
        for fact in newFacts:
             
            if type(fact) == Fact:

 #               newLabel = 'F'+str(self.curFactNum)
                newLabel = self.newLabel()
                self.factLabels[newLabel] = fact
                fact.label = newLabel
                
                self.facts.append(fact)
                if fact.equals(self.goal): #we have a new instance of our goal
 #                   print("HERE")
                    self.goalDisCombos.append(fact.disAncestors)
                    self.updateGoalAchieved(fact)
                    #self.goalLabel = fact.label
                    #UPDATE WIN CONDITION
                 
            if type(fact) == Disjunction:
 #               newLabel = 'D'+str(self.curFactNum)
                newLabel = self.newLabel(letter = 'D')
                self.factLabels[newLabel] = fact
                fact.label = newLabel               
                self.disjunctions.append(fact)

                for i in range(0,len(fact.facts)):
                    subFact = fact.facts[i]
                    subFact.dependencies = [fact.label] #a subfact of a disjunction depends on the disjunction
                    subFact.disAncestors = set(fact.disAncestors)
                    subFact.disAncestors.add( (fact.label, i) )
                    
                self.addNewFacts(fact.facts)               
                 
   #         self.curFactNum += 1
 
    def applyStdThm(self, thm, facts):
        valid = True
        if len(facts) != len(thm.facts):
            valid = False
        matching = {}
        for pair in zip(facts,thm.facts):
            inFact = pair[0]
            thmFact = pair[1]
            if inFact.name != thmFact.name:
                valid = False
            if len(inFact.args) != len(thmFact.args):
                valid = False
            for argPair in zip(inFact.args, thmFact.args):
                inArg = argPair[0]
                thmArg = argPair[1]

                #added
                if thmArg[0] == '*':
                    if inArg != thmArg[1:]:
                        print("exact match expected")
                        valid = False
                    continue #don't bother updating the matching dict

                if thmArg in matching:
                    if matching[thmArg] != inArg:
                        valid = False
                else:
                    matching[thmArg] = inArg
     
        if not valid:
 #           print("invalid application of theorem")
            return False
     
        conclusions = []
        for conc in thm.conclusions:
            newFactArgs = [ matching[x] for x in conc.args ]
            newFact = Fact(conc.name, newFactArgs)
            conclusions.append(newFact)
 
        return conclusions
 
    #apply a theorem or hypertheorem, then add the new facts to the environment
    #returns False if the theorem application was invalid
    def applyThm(self,thm, facts):

        #check to make sure that we're never applying two facts from the same disjunction
        usedDisjunctionFacts = set.union(*[f.disAncestors for f in facts])
        usedDisjunctionDict = dict(usedDisjunctionFacts)
        valid = True
        for d , i in usedDisjunctionFacts:
            if usedDisjunctionDict[d] != i:
                valid = False
        if not valid:
            print("Invalid use of disjunction facts")
            return False           
        
        if type(thm) is Theorem:
            newFacts = self.applyStdThm(thm, facts)
        if type(thm) is HyperTheorem:
            newFacts = thm.rule(facts)
        if newFacts == False:
            print("error applying theorem")
            return

        newDisAncestors = set.union( *[fact.disAncestors for fact in facts] )           
        dependencyLabels = [fact.label for fact in facts]       
        for newFact in newFacts:
            newFact.dependencies = dependencyLabels #update the immediate dependencies for the concluded fact
            newFact.concThm = thm
            newFact.disAncestors = newDisAncestors #union of all the disjunction ancestors of all its predecessors

        

        
            
        self.processNewFacts(newFacts) #replace any ?'s 
        self.addNewFacts(newFacts)

        for f in list(newFacts):
            if type(f) == Disjunction:
                newFacts += f.facts #add in the facts from disjunctions

        return newFacts

    #look for any ? symbols in the list of facts, and generate symbols for them
    #replace the question marks in the list of facts
    def processNewFacts(self, newFacts):
        symDict = {}

        #first break up the disjunctions into their component facts
        simpleFactList = []
        for fact in newFacts:
            if type(fact) == Fact:
                simpleFactList.append(fact)
            elif type(fact) == Disjunction:
                simpleFactList += fact.facts
            else:
                print("not Fact or Disjunction")

        for fact in simpleFactList:
            args = fact.args
            for i in range(0,len(args)):
                sym = args[i]

                if sym == None:
                    print("error")
                    fact.doPrint()
                    self.execCommand("display")
                
                if sym[0] == '?':
                    #print("question mark detected")
                    if sym not in symDict:
                        newSymbol = self.generateNewSymbol()
                        #print("newSymbol: ", newSymbol)
                        symDict[sym] = newSymbol
                    args[i] = symDict[sym]

    #produce a new symbol
    #a symbol is a string consisting of an uppercase letter followed by a sequence of digits
    def generateNewSymbol(self):
        try:
            while(True):
                self.curSuffix
                suffix = ""
                if self.curSuffix != 0:
                    suffix = str(self.curSuffix)
                newSymbol = self.curLetter + suffix
                if self.curLetter == 'Z':
                    self.curLetter = 'A'
                    self.curSuffix += 1
                else:
                    self.curLetter = chr(ord(self.curLetter) + 1) #increment curLetter
                if newSymbol not in self.symbolSet:
                    if newSymbol == None:
                        print("error: returning None")
                    return newSymbol
        except AttributeError: #slightly unusual structure
            self.curLetter = 'A'
            self.curSuffix = 0
            return self.generateNewSymbol()


    #enter into case mode using a particular disjunction
   # def enterCases(self, dis):
        
#        self.caseChain.append(dis) #keep a list of all cases being performed
#        self.solvedCases.append([]) # for each disjunction in cases, keep track of which indices have been solved (IN GENERAL SHOULD LOOK THIS UP)

        #add new fact to the list of facts
#        self.curIndices.append(0)

#    def advanceCases(self):
        
        
        


 
    #print facts together with their labels
    def printFacts(self):
         
        for lbl in self.factLabels:
            fact = self.factLabels[lbl]
            fact.doPrint()
            print()
 
    def execCommand(self, cmd):
        cmdList = cmd.split()
        cmdName = cmdList[0]
        cmdArgs = cmdList[1:]
 
        if cmdName == 'apply':
            thmName = cmdArgs[0]
            if thmName in self.theorem_name_dict:
                thm = self.theorem_name_dict[thmName]
            else:
                print("theorem name not recognized")
                return
            thmArgs = cmdArgs[1:] #list of fact labels
            inFacts = [ self.factLabels[lbl] for lbl in thmArgs] #the corresponding list of facts
            self.applyThm(thm, inFacts)
            return
 
        #case disjunction index

 
 
        #an easier-to-implement version of case
        #all or nothing: either prove the result by iterating through some cases, or fail
        if cmdName == 'cases':

            print("DEPRECATED")
            return
 
            if(self.caseDepth >= 1):
                print("only one level of cases supported")
                return
             
            lbl = cmdArgs[0]
            dis = self.factLabels[lbl]
            if type(dis) != Disjunction:
                print("not a disjunction")
                return
 
            self.startCases(dis)
            return
 
        if cmdName == 'conclude':

            print("DEPRECATED")
            return
            
            conclusionLbl = cmdArgs[0]
            conclusion = self.factLabels[conclusionLbl]
            if not conclusion.equals(self.goal):
                print("conclusion is not the goal")                
                return
 
            if self.caseDepth == 0: #not in any cases
                print("goal achieved")
 
            if self.caseDepth > 0:
                done = self.caseSolved()
                if done:
                    print("goal achieved")
                            
            return
             
        if cmdName == 'display':
            self.printFacts()
            return
 
        if cmdName == 'exit':
            return False
 
        print("Unkown Command")
 
    def startCases(self, dis):
        self.numCases = len(dis.facts) #how many cases to deal with
        self.solvedCases = 0 #how many cases have been solved
        self.caseDepth += 1
        self.caseDis = dis
        self.caseFact = (dis.facts[self.solvedCases]).copy()
        self.addNewFacts([self.caseFact])
 
    #called when a new case has been verified to be solved
    #return True if all cases have been exhausted
    def caseSolved(self):
        self.solvedCases += 1
        self.removeFactsByDepth(self.caseDepth)
        if self.solvedCases == self.numCases:
            done = True
            self.caseDepth -= 1
        else:
            done = False
            self.caseFact = ((self.caseDis).facts[self.solvedCases]).copy()
            self.addNewFacts([self.caseFact])
        return done
 
    #remove facts at a particular depth
    def removeFactsByDepth(self, D):
        factLabels = self.factLabels
        for lbl in dict(factLabels): #copy first, slightly annoying
            fact = factLabels[lbl]
            if fact.depth == D:
                self.removeFact(lbl)
                 
    def removeFact(self,lbl):
        fact = self.factLabels[lbl]
        self.facts.remove(fact)
        del(self.factLabels[lbl])

    #print a log describing how a fact was reached

    def printDerivation(self, factLabel, derivedFactLabels = set() ):

        #backtrack through the depency graph
        #mark the goal with a depth of 0 (0 is the deepest - we're measuring from the bottom of the ocean)
        #the depth of any other fact is 

        fact = self.factLabels[factLabel]
        if fact.dependencies != []:  #the fact was not an assumption
            thm = fact.concThm
            thmName = thm.name

            #make sure all the hypotheses have been proven
            for label in fact.dependencies:
                if label not in derivedFactLabels:
                    self.printDerivation(label, derivedFactLabels)

            print("Applying theorem ", thmName, " to ", fact.dependencies, " we have: ")
            fact.doPrint()
            print()
            
            derivedFactLabels.add(factLabel)
                       
        else:
            print("By assumption we have: ")
            fact.doPrint()
            print()
            derivedFactLabels.add(factLabel)
            
        
        
        
             
 
#given a list of facts and the input structure to a theorem, output all possible tuples of input facts
# (is this #P-hard?)
 
#input_struc is the structure of the input that the theorem takes
#takes the form of a list of facts
#facts is the universe of facts available to be matched
#returns a list of (fact lists), one for each matching combination
#(this could make the data structures rather large.  might be better to instead return lists of fact labels?)
#(a more compact data structure could take the form of a tree)

#if newFacts is not None, then only look for matches containing newFacts
def match_facts_to_theorem(thm_facts, facts, newFacts = None):

    if newFacts == None:
        newFacts = facts #just assume every fact is new

    curMatches = [[]] #the current list of (lists of facts which match the first i theorem hypotheses)
    dicts = [{}] #list of (matching dicts) corresponding to the lists in curMatches
    usesNewList = [False]
    #build a dictionary consisting of all the matches to each theorem hypothesis
    for i in range(0,len(thm_facts)):       
        newCurMatches = []
        newDicts = []
        newUsesNewList = []
        for match,match_dict, usesNew in zip(curMatches,dicts, usesNewList):
            newFactMatches, newFactDicts = match_facts_to_template(thm_facts[i], facts, initMatchDict = match_dict)          
            for newMatch,newDict in zip(newFactMatches,newFactDicts):
                newCurMatches.append( list(match) + [newMatch])               
                newDicts.append(dict(newDict))
                newUsesNewList.append( usesNew or (newMatch in newFacts))
        curMatches = newCurMatches
        dicts = newDicts
        usesNewList = newUsesNewList

    ret = []
    for match, usesNewFact in zip(curMatches, usesNewList):
        if usesNewFact:
            ret.append(match)
    return ret

         
#find all facts that match a given template structure
#also returns the associated matching dict
#optional argument initMatchDict gives literals corresponding to a subset of arguments in template
#not necessarily as efficient as possible
def match_facts_to_template(template, facts, initMatchDict = {}):
    matches = []
    dicts = []
    templateName = template.name
    templateArgs = template.args
     
    for fact in facts:
        if fact.name != templateName: continue
        if len(fact.args) != len(templateArgs): continue
        #length and name match
        matchDict = dict(initMatchDict) #make a copy
 
        match = True
        for argPair in zip(templateArgs, fact.args):
            tempArg = argPair[0]
            factArg = argPair[1]

            if tempArg[0] == "*":
                if tempArg[1:] != factArg:
                    match = False
                    break
            
            if tempArg not in matchDict:
                matchDict[tempArg] = factArg
            elif matchDict[tempArg] != factArg:
                match = False
                break
        if match:
            matches.append(fact)
            dicts.append(dict(matchDict))
    return [matches,dicts]


def autoSolve(pfEnvir):

    thmMatches = {} #dict mapping theorems in the environment to lists of fact matches
    for thm in pfEnvir.theorems:
        thmMatches[thm] = match_facts_to_theorem(thm.facts, pfEnvir.facts)

    while(True):
        #pick one of the matches according to some procedure
        #"breadth-first" approach
        #should remove things once they're already applied

        #for dis in pfEnvir.disjunctions:
        encounteredMatch = False #check if we're out of matches
        
        newFacts = []
        
        
        for thm in thmMatches:

 #           print("new thm")
            for match in list(thmMatches[thm]):
 #               print("   new match")
                encounteredMatch = True #did we actually do anything with the match?
#                print("   about to apply ", thm.name)
 #               for f in match:
 #                   f.doPrint()
                factsFromTheorem = pfEnvir.applyThm(thm,match)
#                print("   applied")
                
 #              if(len(factsFromTheorem) > 0): encounteredMatch = True

                if factsFromTheorem: #sometimes the theorem match might be invalid. FIX?
                                    #FIX move encounteredMatch here
                    newFacts += factsFromTheorem
                thmMatches[thm].remove(match) #prevent reapplying theorems
            
        if not encounteredMatch:
            print("Out of facts")
            pfEnvir.execCommand("display")
            return
 #       else:
 #           print("not out of facts yet")


        for thm in pfEnvir.theorems:
            thmMatches[thm] += match_facts_to_theorem(thm.facts, pfEnvir.facts, newFacts)

        if pfEnvir.goalAchieved:
            print("DONE!")
            pfEnvir.execCommand("display")
            return
        else:
          #  print("******************************************")
           # pfEnvir.execCommand("display")
            #print("******************************************")
            print("next iteration")
                
                
        
################################### FACT GENERATORS ######################################        

#G is a group
def group(G):
    return Fact("group", [G])

#the order of G is n
def order(G,n):
    return Fact("order", [G, n])

#P is a sylow p-subgroup of G
def sylow_p_subgroup(P, p, G):
    return Fact("sylow_p_subgroup", [P, p, G])

#A is the alternating group on n letters
def alternating_group(A, n):
    return Fact("alternating_group", [A, n])

#the number of sylow p-subgroups of G is n
def num_sylow(p, G, n):
    return Fact("num_sylow", [p,G,n])

#G is simple
def simple(G):
    return Fact("simple", [G])

#G is not simple
def not_simple(G):
    return Fact("not_simple", [G])

#H is a subgroup of G
def subgroup(H, G):
    return Fact("subgroup", [H,G])

#m divides n
def divides(m, n):
    return Fact("divides", [m,n])

#a false statement
def false():
    return Fact("false", [])

#H's index in G is n
def index(G, H, n):
    return Fact("index", [G, H, n])

#G acts transitively on a set of size n
def transitive_action(G, n):
    return Fact("transitive_action", [G, n])

#number of elements of order p^k for some k>0 is at least N
def order_pk_lower_bound(G, p, N):
    return Fact("order_pk_lower_bound", [G, p, N])



def OR(f1,f2):
    return Disjunction([f1,f2])
    
    
####################################### THEOREMS #######################################
             
 

#sylow's theorem
import sylow2
inFacts = [ group('G'), order('G','n')]
def rule(facts):
    conclusions = []
    groupName = facts[0].args[0]
    groupOrder = int(facts[1].args[1])
    for p in sylow2.primeFactors(groupOrder):
        sylowOrder = p ** sylow2.max_p_divisor(groupOrder, p)
 #       conclusions.append(Fact("sylow_p_subgroup", ['?'+ str(p), str(p), groupName]))
        conclusions.append(sylow_p_subgroup('?' + str(p), str(p), groupName) )
        conclusions.append(order('?' + str(p), str(sylowOrder)) )
        n_pList = sylow2.num_sylow(p,groupOrder)
        disFacts = []
        for n_p in n_pList:
            #conclusions.append(Fact("int_lit", [n_p]))
            disFacts.append(Fact("num_sylow", [str(p), groupName, str(n_p)]))
        if(len(disFacts) == 1):
            conclusions.append(disFacts[0]) #minor optimization
        else:
            dis = Disjunction(disFacts)
            conclusions.append(dis)
    return conclusions
sylowTheorem = HyperTheorem(inFacts,rule, "sylow")



#single sylow subgroup
inFacts = [Fact("sylow_p_subgroup", ['H', 'p', 'G']), Fact("num_sylow", ['p', 'G', '*1']), Fact("order", ['G', 'n'])]
def rule(facts):
    conclusions = []
    G = facts[0].args[2]
    p = int(facts[0].args[1])
    n = int(facts[2].args[1]) #take off the asterisk
    p_power = True
    while n != 1:
        if n % p != 0: 
            p_power = False
            break
        n = n // p
    if not p_power:
        conclusions = [Fact("not_simple", [G])]
    return conclusions
singleSylow_notSimple = HyperTheorem(inFacts, rule, "single_sylow_normal")

#simple + not_simple = false
inFacts = [Fact("simple", ['G']), Fact("not_simple", ['G'])]
outFacts = [Fact("false",[])]
simple_not_simple = Theorem(inFacts,outFacts,"not_simple")

#embed into A_n
inFacts = [Fact("num_sylow", ['p', 'G', 'n_p']), Fact("simple", ['G'])]
def rule(facts):
    #print("applying embed in An")
    conclusions = []
    n_p = int(facts[0].args[2])
    G = facts[0].args[1]
    if n_p > 1:
        #conclusions = [Fact("subgroup", [G, '?alt']), Fact("alternating_group", ['?alt', str(n_p)]) ]
        conclusions = [subgroup(G, '?alt'), alternating_group('?alt', str(n_p)) ]
    return conclusions
embed_in_An = HyperTheorem(inFacts,rule, "embed_An")

import math
inFacts = [alternating_group('A', 'n')]
def rule(facts):
    A = facts[0].args[0]
    n = int(facts[0].args[1])

    if n > 1000:  #huge factorial computions are extremely slow/impossible
                  #Ugly, but it works.  Other approaches?
        return []
    
    if n == 1:
        order = 1
    else:
        order = math.factorial(n)//2
    conclusions = [Fact("order", [A, str(order)])]
    return conclusions
alternating_order = HyperTheorem(inFacts,rule, "alternating_order")

#order of a subgroup divides the order of the group
inFacts = [Fact("subgroup", ['H', 'G']), Fact("order", ['H', 'n']), Fact("order", ['G', 'm'])]
outFacts = [Fact("divides", ['n', 'm'])]
lagrange = Theorem(inFacts, outFacts, "lagrange")

#check if m divides n
inFacts = [Fact("divides", ['m','n'])]
def rule(facts):
    m = int(facts[0].args[0])
    n = int(facts[0].args[1])
    conclusions = []
    if n % m != 0: conclusions.append(Fact("false", []))
    return conclusions
divides_contradiction = HyperTheorem(inFacts,rule,"divides_contradiction")

#an alternating group of order n > 5 is simple
inFacts = [alternating_group('A', 'n')]
def rule(facts):
    
 #   print("in alternating order")
    
    conclusions = [] #needing this is annoying
    n = int(facts[0].args[1])
    if n >= 5:
        A = facts[0].args[0] #this step is also annoying
        conclusions = [simple(A)]
    return conclusions
alternating_simple = HyperTheorem(inFacts, rule, "alternating_simple")

#index of a subgroup
inFacts = [subgroup('H','G'), order('H', 'm'), order('G', 'n')]
def rule(facts):
    conclusions = []
    m = int(facts[1].args[1])
    n = int(facts[2].args[1])
    H = facts[0].args[0]
    G = facts[0].args[1]
    if n % m == 0:
        i = str(n // m)
        conclusions = [index(G, H, i)]
    return conclusions
subgroup_index = HyperTheorem(inFacts, rule, "subgroup_index")

#G acts transitively on the cosets of H
inFacts = [index('G', 'H', 'n')]
outFacts = [transitive_action('G', 'n')]
coset_action = Theorem(inFacts, outFacts, "coset_action")

######
inFacts = [transitive_action('G', 'n'), simple('G')]
def rule(facts):
    conclusions = []
    n = int(facts[0].args[1])
    if n > 1:
        conclusions = [subgroup('G', '?alt'), alternating_group('?alt', str(n))]
    return conclusions
simple_group_action = HyperTheorem(inFacts, rule, "subgroup_index")

#counting elements of order p^k
inFacts = [sylow_p_subgroup('P', 'p', 'G'), num_sylow('p', 'G', 'n_p'), order('P','pk')]
def rule(facts):
    G = facts[0].args[2]
    p = int(facts[0].args[1])
    P = facts[0].args[0]
    n_p = int(facts[1].args[2])
    pk = int(facts[2].args[1])
    if pk == p: #P is cylic of prime order
        lower_bound = (p-1) * n_p
    else: #not cyclic of prime order
        if n_p == 1:
            lower_bound = pk - 1
        else:
            lower_bound = pk #probably not optimal
    conclusions = [order_pk_lower_bound(G, str(p), str(lower_bound))]
    return conclusions

count_order_pk_elements = HyperTheorem(inFacts, rule, "count_order_pk_elements")

#getting a contradiction by counting
#really should be varargs
inFacts = [order_pk_lower_bound('G', 'p1', 'N1'),order_pk_lower_bound('G', 'p2', 'N2'), order('G','n')]
def rule(facts):
    print("COUNTING")
    conclusions = []
    p1 = int(facts[0].args[1])
    p2 = int(facts[1].args[1])
    #p3 = int(facts[2].args[1])
    N1 = int(facts[0].args[2])
    N2 = int(facts[1].args[2])
   # N3 = int(facts[2].args[2])
    n = int(facts[2].args[1])
    #if p1 == p2 or p1==p3 or p2==p3: 
      #  return [] #not actually a good approach
    if p1 == p2:
        return []

    if N1 + N2 + 1 > n: #too many elements
        #print("CONTRADICTION")
       # print("N1,N2,N3: ", N1, N2, N3)
        #print("p1,p2,p3: ", p1, p2, p3)
        return [false()]
    else:
        return conclusions
counting_contradiction = HyperTheorem(inFacts, rule, "counting_contradiction")
    

thmList = [#sylowTheorem,
           singleSylow_notSimple,
           simple_not_simple,
           #alternating_order,
           #embed_in_An,
           #lagrange,
           #divides_contradiction,
           #alternating_simple,
           #subgroup_index,
           #coset_action,
           #simple_group_action,
           count_order_pk_elements,
           counting_contradiction
           ]

thmNames = {#"sylow":sylowTheorem,
            "not_simple":singleSylow_notSimple,
            "simple_not_simple":simple_not_simple,
            #"alternating_order":alternating_order,
            #"embed_An": embed_in_An,
            #"lagrange":lagrange,
            #"divides_contradiction":divides_contradiction,
            #"alternating_simple": alternating_simple,
            #"subgroup_index": subgroup_index,
            #"coset_action": coset_action,
            #"simple_group_action": simple_group_action,
            "count_order_pk_elements": count_order_pk_elements,
            "counting_cont": counting_contradiction
            }


########################################## TESTING #####################################################     
def test1():

    #subgroup_trans theorem
    facts = [ Fact("subgroup", ['A', 'B']), Fact("subgroup", ['B', 'C']) ]
    conclusions = [Fact("subgroup", ['A', 'C'])]
    subgroup_trans = Theorem(facts, conclusions, "subgroup_trans")

    fact2 = Fact("subgroup", ['X', 'Y'])
    fact3 = Fact("subgroup", ['X','Z'])
    d1 = Fact("subgroup", ['Y','A'])
    d2 = Fact("subgroup", ['Z','A'])
    dis = Disjunction([d1,d2])
 
    facts = [fact2,fact3, dis]
    theorems = [subgroup_trans]
    theoremNames = {"subgroup_trans" : subgroup_trans}
    goal = Fact("subgroup", ['X','A'])
 
    pfEnvir = ProofEnvironment(facts,theorems,theoremNames, goal)
 
    running = True
   # while(running != False):
#        cmd = input()
#        running = pfEnvir.execCommand(cmd)
    pfEnvir.execCommand("apply subgroup_trans F1 F4")
    pfEnvir.execCommand("display")
    pfEnvir.execCommand("apply subgroup_trans F0 F3")
    if(pfEnvir.goalAchieved):
        print("DONE")

def test2():

    global thmList
    global thmNames

    fact1 = Fact("group", ['G'])
    fact2 = Fact("order", ['G', '6'])
    fact3 = Fact("simple", ['G'])
    facts = [fact1, fact2, fact3]

    goal = Fact("false", [])
 
    pfEnvir = ProofEnvironment(facts,thmList,thmNames, goal)
 
    running = True
    while(running != False):
        cmd = input()
        running = pfEnvir.execCommand(cmd)

def matchingTest():
    def foo(first, second, third):
        return Fact("foo", [first, second, third])
    def bar(a, b, c):
        return Fact("bar", [a,b,c])

    template = foo('W','X', 'W')
   # facts = [foo('A','B','C'), foo('D','C','D'), foo('C','A','A'), foo('A','C','A'), bar('x','y','x'), bar('x','x','x'), bar('x','x','u')]
    facts = [foo('A','B','C'), foo('D','E','F')]
    thmFacts = [foo('X','Y','Z'), foo('X','Y','Z')]


    matches = match_facts_to_theorem(thmFacts,facts,[foo('A','B','C')])

    print("in matchingTest")
    for match in matches:
        for fact in match:
            fact.doPrint()
        print(" ")
        
 #   matches,dicts = match_facts_to_template(template, facts)
#    for match in matches:
#       match.doPrint()
#    print(dicts)

def autoTest():
    facts = [ Fact("subgroup", ['A', 'B']), Fact("subgroup", ['B', 'C']) ]
    conclusions = [Fact("subgroup", ['A', 'C'])]
    subgroup_trans = Theorem(facts, conclusions, "subgroup_trans")

    fact1 = Fact("subgroup", ['X', 'Y'])
    fact2 = Fact("subgroup", ['Y','Z'])
    fact3 = Fact("subgroup", ['Z', 'A'])
    fact4 = Fact("subgroup", ['A', 'B'])
    fact5 = Fact("subgroup", ['B', 'C'])
    fact6 = Fact("subgroup", ['C','D'])
    fact7 = Fact("subgroup", ['D', 'E'])
    fact8 = Fact("subgroup", ['E', 'F'])
 
    facts = [fact4, fact7, fact1, fact3, fact2, fact6, fact5, fact8]
    theorems = [subgroup_trans]
    theoremNames = {"subgroup_trans" : subgroup_trans}
    goal = Fact("subgroup", ['X','F'])
 
    pfEnvir = ProofEnvironment(facts,theorems,theoremNames, goal)

    autoSolve(pfEnvir)

def autoTest2():
    global thmList
    global thmNames

    while(True):
        order = input("Enter a group order: ")
        fact1 = Fact("group", ['G'])
        fact2 = Fact("order", ['G',order])
        fact3 = Fact("simple", ['G'])
 
        facts = [fact1, fact2, fact3]
        goal = Fact("false", [])
 
        pfEnvir = ProofEnvironment(facts,thmList,thmNames, goal)

        autoSolve(pfEnvir)
        

def easyDisTest():
    def subgroup(A,B):
        return Fact("subgroup", [A,B])
    def OR(f1,f2):
        return Disjunction([f1,f2])

    facts = [ Fact("subgroup", ['A', 'B']), Fact("subgroup", ['B', 'C']) ]
    conclusions = [Fact("subgroup", ['A', 'C'])]
    subgroup_trans = Theorem(facts, conclusions, "subgroup_trans")

    facts = [OR(subgroup('A','B'), subgroup('A','X')),
 #            OR(subgroup('A','B'), subgroup('A','X')),
             subgroup('B','D'),
             subgroup('X','D')]
    theorems = [subgroup_trans]
    theoremNames = {"subgroup_trans" : subgroup_trans}
    goal = subgroup('A','D')
 
    pfEnvir = ProofEnvironment(facts,theorems,theoremNames, goal)
    autoSolve(pfEnvir)
    

def autoDisTest():

    def subgroup(A,B):
        return Fact("subgroup", [A,B])
    def OR(f1,f2):
        return Disjunction([f1,f2])
    
    facts = [ Fact("subgroup", ['A', 'B']), Fact("subgroup", ['B', 'C']) ]
    conclusions = [Fact("subgroup", ['A', 'C'])]
    subgroup_trans = Theorem(facts, conclusions, "subgroup_trans")

 
    facts = [OR(subgroup('A','B'), subgroup('C','D')),
             OR(subgroup('B','F'), subgroup('D','F')),
             subgroup('B','D'),
             subgroup('D','B'),
             subgroup('X','A'),
             subgroup('X','C') ]
    
    theorems = [subgroup_trans]
    theoremNames = {"subgroup_trans" : subgroup_trans}
    goal = subgroup('X','F')
 
    pfEnvir = ProofEnvironment(facts,theorems,theoremNames, goal)
    autoSolve(pfEnvir)

def alternatingTest():
    global thmList
    global thmNames
#    thmList = [embed_in_An]
 #   thmNames = ["embed_in_An", embed_in_An]
    fact1 = Fact("simple", ['G'])
    fact2 = Fact("num_sylow", ['3', 'G', '4'])
    fact3 = Fact("order", ['G', '12'])
    goal = Fact("false",[])

    pfEnvir = ProofEnvironment([fact1,fact2,fact3], thmList, thmNames, goal)
    autoSolve(pfEnvir)

def orderCountingTest():
    global thmList
    global thmNames
    
    fact1 = group('G')
    fact2 = order('G', '30')
    fact3 = num_sylow('5', 'G', '6')
    fact4 = OR(num_sylow('3', 'G', '10'), num_sylow('3','G', '1'))
    fact5 = sylow_p_subgroup('P5', '5', 'G')
    fact6 = sylow_p_subgroup('P3', '3', 'G')
    fact7 = order('P5', '5')
    fact8 = order('P3', '3')
    fact9 = simple('G')

    factList = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8]
    pfEnvir = ProofEnvironment(factList, thmList, thmNames, false())
    autoSolve(pfEnvir)




orderCountingTest()
#autoTest2()
