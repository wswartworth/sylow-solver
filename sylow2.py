import math
 
prime_list = []
 
#computes the possible numbers of sylow-p subgroups in a group of order n
#too slow for huge orders
def num_sylow(p, n):
        n_p = []
        for i in range(0,n):
                if (i % p == 1) and (n % i == 0):
                        n_p.append(i)
        return n_p
 
#is the sylow p automatically normal?
def p_killable(p,n):
 
        div = divisors(n)
        div.remove(1)
        for d in div:
                if(d % p == 1): return False
        return True
 
#is p prime?
def prime(p):
        if p == 1: return False
        u = int(math.sqrt(p)) + 1
        for i in range( 2, u ):
                if p % i == 0: return False
        return True
 
#list of primes up to and including n
#could be much faster
def primes(n):
        primes = []
        for i in range(1,n+1):
                if prime(i): primes.append(i)
        return primes
 
#returns k, maximal such that p^k divides n
def max_p_divisor(n,p):
        k=0
        while(n % p == 0):
                k += 1
                n = n//p #probably not as fast as possible
        return k
 
#slower than necessary
def primeFactorization(n):
        global prime_list
        factorization = []
        for p in prime_list:               
                if n % p == 0:
                        factorization.append([p,max_p_divisor(n,p)])
        return factorization
 
#def primeFactors(n):
#    factorization = primeFactorization(n)
#    return [a[0] for a in factorization]
 
def divisors(n):
        #factorization = primeFactorization(n)
        #divisors = [1]
        #for entry in factorization:
        #    p = entry[0]
        #    k = entry[1]
        #    new_divisors = []
        #    for d in divisors:
        #        for i in range(1,k+1):
        #            new_divisors.append( d * (p ** i) )
        #    divisors = divisors + new_divisors
        #return divisors
        divs = []
        for i in range(1,n+1):
            if n % i == 0:
                divs.append(i)
        return divs
                 
             
 
#is there automatically a normal sylow-p for some p?
def sylow_killable(n):
 
        if n == 1: return True
 
        p_factors = primeFactors(n)
        p_factors.reverse() #try big primes first
 
        for p in p_factors:
                if p_killable(p,n): return True
 
        return False
 
def primeFactors(n):
        factors = []
        for i in range(1,n+1):
                if n % i == 0:
                        if prime(i):
                                factors.append(i)
        return factors
                                 

#print(divisors(12))
#print out the "interesting" group orders
 
#upper = int(input("interesting orders up to... : "))
 
#prime_list = primes(upper)
 
#print("killable: ", sylow_killable(upper))
 
#print(divisors(n))
 
#count = 0
#for n in range(1,upper):
#        if n % 1000 == 0: print(n)
#        if(not sylow_killable(n)):
#                print(n)
#                count += 1
#print("count: ", count)