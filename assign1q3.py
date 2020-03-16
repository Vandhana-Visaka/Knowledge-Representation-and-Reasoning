# ///////////Written by Vandhana Visakamurthy for COMP4418 - Assignment 1 ///////
####################AUTOMATED THEOREM PROVER ##################################
import sys
sequent = sys.argv[1]
LHS = sequent.split('seq')[0]
RHS = sequent.split('seq')[1]
#The number of clauses in LHS and RHS can be identified using the no. of commas
no_of_LHS_clauses = len(LHS.split(','))
no_of_RHS_clauses = len(RHS.split(','))
#The Left and Right Hand side of the equation is stripped off of any unnecessary spaces
LHS = LHS.strip()
RHS = RHS.strip()
#The '[]' braces are removed from the left and right strings and the clauses are split and stores as lists
LHS = LHS.replace('[','')
LHS = LHS.replace(']','')
LHS = LHS.split(',')
RHS = RHS.replace('[','')
RHS = RHS.replace(']','')
RHS = RHS.split(',')
#print(LHS)
#print(RHS)

#visited list keeps track of all evaluated expressions
visited = []
#Sequences list stores all the intermediate sequences and the final sequences
Sequences = []
#Rules keeps track of all the rules applied in each step
Rules = []

Sequences.append(sequent)
Rules.append('-Input-')

#Logical Matcher is a function to check the basic validity of the input before matching it with rules
def Logical_Checker(LHS,RHS):
    #This checks if elements exist on both sides of the seq using string manipulation
    L = []
    R = []
    count = 0
    for n in LHS:
        n = n.replace('and',' ')
        n = n.replace('or',' ')
        n = n.replace('imp',' ')
        n = n.replace('iff',' ')
        n = n.strip()
        L.append(n)
    for n in RHS:
        n = n.replace('and',' ')
        n = n.replace('or',' ')
        n = n.replace('imp',' ')
        n = n.replace('iff',' ')
        n = n.strip()
        R.append(n)
    #print(L,R)
    if '' in L and len(L) == 1:
        if 'neg' in R[0]:
            return True
        else:
            return False
    elif '' in R and len(R) == 1:
        if 'neg' in L[0]:
            return True
        else:
            return False
    else:
        L[0] = L[0].replace('neg','')
        L[0] = L[0].replace('(','')
        L[0] = L[0].replace(')','')
        R[0] = R[0].replace('neg','')
        R[0] = R[0].replace('(','')
        R[0] = R[0].replace(')','')
        a = L[0].split()
        b = R[0].split()
        #print(a,b)
        #count keeps track if elements occur on both sides of the expression
        for n in a:
            if n in b:
                count+=1
        for n in b:
            if n in a:
                count+=1
        #print(count)
        if count == 0:
            return False
        else:
            return True

#A function called Rule Matcher is used to identify the brackets and the rules to evaluate the sequence
def Rule_Matcher(LHS,RHS):
    #print(LHS,RHS)
    #the bracket macther is used as a flag value to count the no. of brackets.
    #this ensures that only operators outside the brackets are evaluated before evaluating the brackets inside
    #the operators within the brackets are skipped until only the brackets are left
    if (RuleP1(LHS,RHS) == True):
        #print('Rule P1')
        #print('QED')
        #Sequences.append('QED')
        Rules.append('Rule P1')
    if (RuleP1(LHS,RHS) == False):
        bracket_matcher = 0;
        for n in LHS:
            for i in range(len(n)):
                if n[i]=='(':
                    bracket_matcher +=1
                elif n[i]==')':
                    bracket_matcher -=1
                else: #for any other element in the sequence
                    if bracket_matcher == 0:
                        if (n[i:i+3] == 'neg'):
                            Rules.append('Rule P2b')
                            RuleP2b(LHS,RHS)
                        if (n[i:i+3] == 'and'):
                            Rules.append('Rule P3b')
                            RuleP3b(LHS,RHS)
                        if (n[i:i+2] == 'or'):
                            Rules.append('Rule P4b')
                            RuleP4b(LHS,RHS)
                        if (n[i:i+3] == 'imp'):
                            Rules.append('Rule P5b')
                            RuleP5b(LHS,RHS)
                        if (n[i:i+3]=='iff'):
                            Rules.append('Rule P6b')
                            RuleP6b(LHS,RHS)
                    if bracket_matcher != 0:
                        #print('check')
                        continue
        #the right hand side of the sequence is then evaluated
        for n in RHS:
            for i in range(len(n)):
                if n[i]=='(':
                    bracket_matcher +=1
                elif n[i]==')':
                    bracket_matcher -=1
                else: #for any other element in the sequence
                    if bracket_matcher == 0:
                        if (n[i:i+3] == 'neg'):
                            Rules.append('Rule P2a')
                            RuleP2a(LHS,RHS)
                        if (n[i:i+3] == 'and'):
                            Rules.append('Rule P3a')
                            RuleP3a(LHS,RHS)
                        if (n[i:i+2] == 'or'):
                            Rules.append('Rule P4a')
                            RuleP4a(LHS,RHS)
                        if (n[i:i+3] == 'imp'):
                            Rules.append('Rule P5a')
                            RuleP5a(LHS,RHS)
                        if (n[i:i+3]=='iff'):
                            Rules.append('Rule P6a')
                            RuleP6a(LHS,RHS)
                    if bracket_matcher != 0:
                        #print('check')
                        continue
    else:
        return
#After the expression is evaluated based on the Rule it is matched with the brackets are removed for further evaluation


#Rule P1 checks if the sequence is in atomic form - that is no operators should be present
def RuleP1(LHS,RHS):
    Left_Truth = []
    Right_Truth = []
    for n in LHS:
        if ('or' not in n) and ('and' not in n) and ('neg' not in n) and ('imp' not in n) and ('iff' not in n):
            Left_Truth.append(True)
        else:
            Left_Truth.append(False)
    for n in RHS:
        if ('or' not in n) and ('and' not in n) and ('neg' not in n) and ('imp' not in n) and ('iff' not in n):
            Right_Truth.append(True)
        else:
            Right_Truth.append(False)

    #print(Left_Truth)
    #print(Right_Truth)
    #the all() is used to check if the entire truth values are true
    if(all(x==True for x in Left_Truth) and all(x==True for x in Right_Truth)):
        #print('Rule P1')
        return True
    else:
        #print('Not valid')
        return False


#P2a evaluates the sequence when 'neg' is in the right hand side of 'seq'
def RuleP2a(LHS,RHS):
    L = []
    R = []
    L = LHS.copy()
    for n in RHS:
        if 'neg' in n:
            temp1 = n.split('neg')[0]
            temp2 = n.split('neg')[1]
            temp1 = temp1.replace(',','')
            temp2 = temp2.replace(',','')
            if '(' in temp1:
                temp1 = temp1.replace('(','')
            if ')' in temp1:
                temp1 = temp1.replace(')','')
            #check for temp2
            if '(' in temp2:
                temp2 = temp2.replace('(','')
            if ')' in temp2:
                temp2 = temp2.replace(')','')
            temp1 = temp1.strip()
            temp2 = temp2.strip()
            R.append(temp1)
            L.append(temp2)
            visited.append(n)
    for x in RHS:
        if x not in visited:
            if '(' in x:
                x = x.replace('(','')
            if ')' in x:
                x = x.replace(')','')
            R.append(x)
    s = '[ ' + ' '.join(x for x in L) + ' ]' + ' seq '  +  '[ ' + ' '.join(x for x in R) + ' ]'
    #print(s)
    Sequences.append(s)
    return Rule_Matcher(L,R)

#P2b evaluates the sequence when 'neg' is in the left hand side of 'seq'
def RuleP2b(LHS,RHS):
    L = []
    R = []
    R = RHS.copy()
    for n in LHS:
        if 'neg' in n:
            temp1 = n.split('neg')[0]
            temp2 = n.split('neg')[1]
            if '(' in temp1:
                temp1 = temp1.replace('(','')
            if ')' in temp1:
                temp1 = temp1.replace(')','')
            #check for temp2
            if '(' in temp2:
                temp2 = temp2.replace('(','')
            if ')' in temp2:
                temp2 = temp2.replace(')','')
            temp1 = temp1.strip(',')
            temp2 = temp2.strip(',')
            L.append(temp1)
            R.append(temp2)
            visited.append(n)
    for x in LHS:
        if x not in visited:
            if '(' in x:
                x = x.replace('(','')
            if ')' in x:
                x = x.replace(')','')
            L.append(x)
    s = '[ ' + ' '.join(x for x in L) + ' ]' + ' seq '  +  '[ ' + ' '.join(x for x in R) + ' ]'
    #print(s)
    Sequences.append(s)
    return Rule_Matcher(L,R)

#p3a evaluates the sequence when 'and' is in the right hand side of 'seq'
def RuleP3a(LHS,RHS):
    R1 = []
    R2 = []
    L = []
    for n in RHS:
        if 'and' in n:
            temp1 = n.split('and')[0]
            temp2 = n.split('and')[1]
            if '(' in temp1:
                temp1 = temp1.replace('(','')
            if ')' in temp1:
                temp1 = temp1.replace(')','')
            #check for temp2
            if '(' in temp2:
                temp2 = temp2.replace('(','')
            if ')' in temp2:
                temp2 = temp2.replace(')','')
            visited.append(n)
    temp1 = temp1.strip()
    temp2 = temp2.strip()
    R1 += temp1
    R2 += temp2
    for x in RHS:
        if x not in visited:
            if '(' in x:
                x = x.replace('(','')
            if ')' in x:
                x = x.replace(')','')
            R1.append(x)
            R2.append(x)
    L = LHS.copy()
    s1 =  '[ ' + ''.join(x for x in L) + ' ]'  + ' seq '  +  '[ ' + ''.join(x for x in R1) + ' ]'
    s2 =  '[ ' + ''.join(x for x in L) + ' ]'  + ' seq '  +  '[ ' + ''.join(x for x in R2) + ' ]'
    #print(s1)
    #print(s2)
    Sequences.append(s1)
    Sequences.append(s2)
    #Rules.append('Rule P3a')
    return Rule_Matcher(L,R1) and Rule_Matcher(L,R2)
#p3b evaluates the sequence when 'and' is in the left hand side of 'seq'
def RuleP3b(LHS,RHS):
    L = []
    R = []
    for n in LHS:
        if 'and' in n:
            temp1 = n.split('and')[0]
            temp2 = n.split('and')[1]
            if '(' in temp1:
                temp1 = temp1.replace('(','')
            if ')' in temp1:
                temp1 = temp1.replace(')','')
            #check for temp2
            if '(' in temp2:
                temp2 = temp2.replace('(','')
            if ')' in temp2:
                temp2 = temp2.replace(')','')
            temp1 = temp1.strip()
            temp2 = temp2.strip()
            L.append(temp1)
            L.append(temp2)
            visited.append(n)
    for x in LHS:
        if x not in visited:
            if '(' in x:
                x = x.replace('(','')
            if ')' in x:
                x = x.replace(')','')
            L.append(x)
    R = RHS.copy()
    s = '[ ' + ' '.join(x for x in L) + ' ]' + ' seq '  + '[ ' + ''.join(x for x in R) + ' ]'
    #print(s)
    Sequences.append(s)
    return Rule_Matcher(L,R)
#Rule P4a evaluates 'or' on the RHS and breaks the statement down
def RuleP4a(LHS,RHS):
    L = []
    R = []
    for n in RHS:
        if 'or' in n:
            #a = n.replace('or',',')
            temp1 = n.split('or')[0]
            temp2 = n.split('or')[1]
            if '(' in temp1:
                temp1 = temp1.replace('(','')
            if ')' in temp1:
                temp1 = temp1.replace(')','')
            #check for temp2
            if '(' in temp2:
                temp2 = temp2.replace('(','')
            if ')' in temp2:
                temp2 = temp2.replace(')','')
            temp1 = temp1.strip()
            temp2 = temp2.strip()
            R.append(temp1)
            R.append(temp2)
            visited.append(n)
    for x in RHS:
        if x not in visited:
            if '(' in x:
                x = x.replace('(','')
            if ')' in x:
                x = x.replace(')','')
            R.append(x)
    L = LHS.copy()
    s = '[ ' + ', '.join(x for x in L) + ' ]' + ' seq '  + '[ ' + ' , '.join(x for x in R) + ' ]'
    #print(s)
    Sequences.append(s)
    return Rule_Matcher(L,R)
#Rule P4b evaluates 'or' on the LHS and breaks the statement down
def RuleP4b(LHS,RHS):
    L1 = []
    L2 = []
    R = []
    for n in LHS:
        if 'or' in n:
            temp1 = n.split('or')[0]
            temp2 = n.split('or')[1]
            if '(' in temp1:
                temp1 = temp1.replace('(','')
            if ')' in temp1:
                temp1 = temp1.replace(')','')
            #check for temp2
            if '(' in temp2:
                temp2 = temp2.replace('(','')
            if ')' in temp2:
                temp2 = temp2.replace(')','')
            visited.append(n)
    #print(temp1)
    #print(temp2)
    temp1 = temp1.strip()
    temp2 = temp2.strip()
    L1.append(temp1)
    L1.append(temp2)
    L2.append(temp1)
    for x in LHS:
        if x not in visited:
            if '(' in x:
                x = x.replace('(','')
            if ')' in x:
                x = x.replace(')','')
            L1.append(x)
            L2.append(x)
    R = RHS.copy()
    s1 = '[ ' + ' '.join(x for x in L1) + ' ]' + ' seq '  + '[ ' + ''.join(x for x in R) + ' ]'
    s2 = '[ ' + ' '.join(x for x in L2) + ' ]' + ' seq '  + '[ ' + ''.join(x for x in R) + ' ]'
    #print(s1)
    #print(s2)
    Sequences.append(s1)
    Sequences.append(s2)
    #Rules.append('Rule P4b')
    return Rule_Matcher(L1,R) and Rule_Matcher(L2,R)
#Rule P4a evaluates 'imp' on the LHS and breaks the statement down
def RuleP5a(LHS,RHS):
    L = []
    R = []
    for n in RHS:
        if 'imp' in n:
            temp1 = n.split('imp')[0]
            temp2 = n.split('imp')[1]
            if '(' in temp1:
                temp1 = temp1.replace('(','')
            if ')' in temp1:
                temp1 = temp1.replace(')','')
            #check for temp2
            if '(' in temp2:
                temp2 = temp2.replace('(','')
            if ')' in temp2:
                temp2 = temp2.replace(')','')
            temp1 = temp1.strip()
            temp2 = temp2.strip()
            visited.append(n)
    L = LHS.copy()
    L.append(temp1)
    R.append(temp2)
    for x in RHS:
        if x not in visited:
            if '(' in x:
                x = x.replace('(','')
            if ')' in x:
                x = x.replace(')','')
            R.append(x)
    s = '[ ' + ' '.join(x for x in L) + ' ]' + ' seq '  +  '[ ' + ' '.join(x for x in R) + ' ]'
    #print(s)
    Sequences.append(s)
    return Rule_Matcher(L,R)
#Rule P5b evaluates 'or' on the RHS and breaks the statement down
def RuleP5b(LHS,RHS):
    L1 = []
    L2 = []
    R1 = []
    R2 = []
    for n in LHS:
        if 'imp' in n:
            temp1 = n.split('imp')[0]
            temp2 = n.split('imp')[1]
            if '(' in temp1:
                temp1 = temp1.replace('(','')
            if ')' in temp1:
                temp1 = temp1.replace(')','')
            #check for temp2
            if '(' in temp2:
                temp2 = temp2.replace('(','')
            if ')' in temp2:
                temp2 = temp2.replace(')','')
            temp1 = temp1.strip()
            temp2 = temp2.strip()
            visited.append(n)
    for x in LHS:
        if x not in visited:
            if '(' in x:
                x = x.replace('(','')
            if ')' in x:
                x = x.replace(')','')
            L1.append(x)
    L1.append(temp2)
    R1 = RHS.copy()
    R2 = RHS.copy()
    R2.append(temp1)
    s1 = '[ ' + ' '.join(x for x in L1) + ' ]' + ' seq '  +  '[ ' + ' '.join(x for x in R1) + ' ]'
    s2 = '[ ' + ' '.join(x for x in L2) + ' ]' + ' seq '  +  '[ ' + ' '.join(x for x in R2) + ' ]'
    #print(s1)
    #print(s2)
    Sequences.append(s1)
    Sequences.append(s2)
    #Rules.append('Rule P5b')
    return Rule_Matcher(L1,R1) and Rule_Matcher(L2,R2)
#Rule P6a evaluates 'iff' on the LHS and breaks the statement down
def RuleP6a(LHS,RHS):
    L1 = []
    L2 = []
    R1 = []
    R2 = []
    for n in RHS:
        if 'iff' in n:
            temp1 = n.split('iff')[0]
            temp2 = n.split('iff')[1]
            if '(' in temp1:
                temp1 = temp1.replace('(','')
            if ')' in temp1:
                temp1 = temp1.replace(')','')
            #check for temp2
            if '(' in temp2:
                temp2 = temp2.replace('(','')
            if ')' in temp2:
                temp2 = temp2.replace(')','')
            temp1 = temp1.strip()
            temp2 = temp2.strip()
            visited.append(n)
    L1 = LHS.copy()
    L1.append(temp1)
    L2 = LHS.copy()
    L2.append(temp2)
    R1.append(temp2)
    R2.append(temp1)
    for x in RHS:
        if x not in visited:
            if '(' in x:
                x = x.replace('(','')
            if ')' in x:
                x = x.replace(')','')
            R1.append(x)
            R2.append(x)
    s1 = '[ ' + ' '.join(x for x in L1) + ' ]' + ' seq '  +  '[ ' + ' '.join(x for x in R1) + ' ]'
    s2 = '[ ' + ' '.join(x for x in L2) + ' ]' + ' seq '  +  '[ ' + ' '.join(x for x in R2) + ' ]'
    #print(s1)
    #print(s2)
    Sequences.append(s1)
    Sequences.append(s2)
    #Rules.append('Rule P6a')
    return Rule_Matcher(L1,R1) and Rule_Matcher(L2,R2)
#Rule P6b evaluates 'iff' on the RHS and breaks the statement down
def RuleP6b(LHS,RHS):
    L1 = []
    L2 = []
    R1 = []
    R2 = []
    for n in LHS:
        if 'iff' in n:
            temp1 = n.split('iff')[0]
            temp2 = n.split('iff')[1]
            if '(' in temp1:
                temp1 = temp1.replace('(','')
            if ')' in temp1:
                temp1 = temp1.replace(')','')
            #check for temp2
            if '(' in temp2:
                temp2 = temp2.replace('(','')
            if ')' in temp2:
                temp2 = temp2.replace(')','')
            visited.append(n)
    temp1 = temp1.strip()
    temp2 = temp2.strip()
    R2 = RHS.copy()
    R2.append(temp1)
    R2.append(temp2)
    for x in LHS:
        if x not in visited:
            if '(' in x:
                x = x.replace('(','')
            if ')' in x:
                x = x.replace(')','')
            L1.append(x)
            R2.append(x)
    L1.append(temp1)
    L1.append(temp2)
    R1 = RHS.copy()
    s1 = '[ ' + ' '.join(x for x in L1) + ' ]' + ' seq '  +  '[ ' + ' '.join(x for x in R1) + ' ]'
    s2 = '[ ' + ' '.join(x for x in L2) + ' ]' + ' seq '  +  '[ ' + ' '.join(x for x in R2) + ' ]'
    #print(s1)
    #print(s2)
    Sequences.append(s1)
    Sequences.append(s2)
    #Rules.append('Rule P6b')
    return Rule_Matcher(L1,R1) and Rule_Matcher(L2,R2)

#The Rule_Matcher calls with the LHS and RHS as arguments
#The Matched Rule is called from within the Rule Rule_Matcher
#The Rule breaks down the expression according to the respective rule
#Then the Rule_Matcher is called upon using the new sequences
#This is recursively done until the entire expression is broken down
#The Sequences are stored in a global list called Sequences after every rule
#The Rules matched at every step are stored in a global list called rules
#To ensure that the values are not evaluated again and to prevent an infinte loop
#The list of all evaluated expressions are stored in the visited list
Rule_Matcher(LHS,RHS)
Sequences.reverse()
Rules.reverse()
solution_flag = 0
if LHS == RHS:
    #this ensures empty strings are matched
    print('true')
elif Logical_Checker(LHS,RHS)==True:
    #this means the input provided is logically valid and can be evaluated
    print('true')
elif Logical_Checker(LHS,RHS)==False:
    #this means the input provided is not logically valid and can be evaluated
    print('false')
    solution_flag = 1
Count = list(range(1,len(Sequences)+1))
solution = "\n".join("{:<2}. {:<60} {}".format(z,x, y) for z, x, y in zip(Count,Sequences, Rules))
#The output is printed only for logically valid expressions
if solution_flag == 0:
    print(solution)
    print('QED.')
