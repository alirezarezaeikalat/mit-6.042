0. A --Proof--: is a method for --ascertaining(find out for certain) the truth--.

1. A --mathematical proof--: is a verification of --proposition (Gozare)-- by a chain of --logical deductions (estentaj)-- from a set 
    of --axioms (Asl)--.

2. --Proposition (Gozare)--: is a statement is either true of false.

3. --Axioms(Asl)--: is a proposition that is assumed to be true.

3.1 A set of axioms should be:
    b. --consistent--: A set of axioms is consistent if no proposition can be proved both true and false

    a. --complete--: A set of axioms is complete if it can be used to prove every proposition is either true or false

4. --Predicate--: is a proposition whose truth depends on the value of variable(s).

5. An --implication-- p => q is true if p is false, or q is true.   => (--implies--)

        --Truth table--:

        P       q       p => q
        T       T          T
        T       F          F
        F       F          T
        F       T          T

 
6. proof by --contradiction--:

    To prove proposition P is true, we assume that P is false, then we use that hypothesis to drive falsehood.

    -- !P => F is T, So not P is false, So P is true-- 

    -prove that radical 2 is irrational: 


    P: radical 2 is irrational

    we assume that P is false, so radical 2 is not irrational:

    sqrt(2) = m/n (fraction in lowest terms)

    2 = m^2 / n^2 => m^2 = 2 * n^2 => m is even (2 | m) => 4 | m^2 => 4 | 2 * n ^ 2

    => 2 | n ^ 2 => m and n are no fraction in the lowest terms

7. proof by induction: 
    
    --actually induction is just a axiom--:

        let  P(n) be a predicate, if P(0) is true and for every n  P(n) => P(n + 1) is true then for every n P(n) is true.


    - proof that for every n 1+2+3+4+ ... + n = n * n(n + 1) / 2

        first step:    If n is 0 then: 0 = 0 * (1) / 2     so P(0) is true

        second step: find the P(n) 

        third step(inductive step): for n >= 0, show P(n) => P(n + 1) is true (the only case this implication can be false is 
        when we assume that P(n) is true)

        Assume P(n) is true, for purpose of verifying the inductive hypothesis:

        we assume 1 + 2 + 3 + ... + n = n(n + 1) / 2

        need to show 1 + 2 + 3 + ... + (n+1) = (n+1) (n+2) /2

        = n (n+1) / 2 + n+1 = (n+1)(n+2) / 2
    
    - proof this 3 | (n^3 - n)
        
        Proof by induction

        P(n):   3 | (n^3 - n)

        base case: 3 | (0 - 0)

        inductive step: for n >= 0 show P(n) => P(n + 1) is true (to show this we assume P(n) is true, because it is the only case
        that whole implication can be false)

        we assume:      3 | (n^3 - n) is true

        we examine      (n+1)^3 - (n+1) = n^3 + 1 + 3n^2 + 3n - n - 1 = n^3 + 3n^2 + 2n = (n^3 - n) + 3n^2 + 3n

[ATTENTION]
--Inductions should not always start at zero--.

8. Using induction for --solving the problem--:
        
    - how to tile the 2^n squares with L shape tiles, that leave one stop for a statue:

        for all n There is a way to tile 2^n * 2^n region with a center square missing

        Pf: proof by induction

        P(n): for all n There is a way to tile 2^n * 2^n region with a center square missing

                

        Base case: P(0): is okay there is only one place for statue

        For n>=0, assume P(n) is true


        2^(n+1) * 2^(n+1) you can divide this square to 4 square with 2^n * 2^n and then if you change the hypothesis to tile with
        L shape with a corner square missing, you can put this corner center of the larger square, and use this to prove the actual 
        proposition,

        but the better approach is to change the predicate to:

                for all n there is a way to tile 2^n 2^n region with --any-- square missing 

[ATTENTION]
This way we change p(n) to more --powerful hypothesis--. This way we can solve the problem much easier.

9. Problem: find sequence of moves that go

    from    A B C   to      A B C
            D E F           D E F
            H G             G H
    
    --Thm--: There is no sequence of legal moves to invert G and H, and return other letters to their original position.

    --invariant--: In order to show that your system can never reach a particular state, It is sufficient to show there is some 
            property called the invariant, that holds at the initial state, and that is preserved by every legal move
            
    To find the invariant for this system, you have analyze the legal moves, to find the invariant property in the system:

        natural order: 

                1 2 3
                4 5 6
                7 8 9
        

        --Lemma 1--: A row move does not change the natural order of the items
        Proof: In a row move, we move an item from cell i into adjacent cell i-1 or i+1, Nothing else moves, Hence the order of 
                the letters is preserved.
        

        --Lemma 2--: A column move changes the relative order of precisely 2 --pair of items--
        Proof: In a column move, we move item from cell i to a blank cell to a cell i+3 or i-3 when an item move position, It change 
        order changes order with 2 item (i-1,i-2 or i+1, i+2)

        Def: A pair of letters L1 and L2 is an inversion, if L1 precedes L2 in the alphabet, but L1 is after L2 in the puzzle.

        --Lemma 3--: during a move it is possible to change the number of inversion by plus 2 or minus 2 or none.
        Proof: Row move: no changes
                Column move: there are three cases:

                        the 2 pairs are in order => so the inversion increase by 2
                        the 2 pairs are inverted => so the inversion decrease by 2
                        there are one of each => so the inversion stay the same
        
        so during a move evenness or oddness of the inverted pairs stay the same.


        --Lemma 4--: In every state reachable from initial condition of this problem, the parity of the number of inversions is odd:
        proof by induction: (all invariant proofs are by induction)
        
        P(n): after any sequence of n moves the parity of the number of inversions is odd
        
        Base case P(0): the number of inversion is 1 (the parity is odd) [check]
        Inductive step: P(n) => P(n+1)

            consider any sequence of n+1 moves (m1 ... mn+1)

            By inductive hypothesis we know that after m1 ... mn the parity is odd

            by lemma 3 we know the parity of number of inversions does not change after one move mn+1
            there for the parity after n+1 moves is odd.
    
        --Proof of theorem--:
            The parity of the inversions in the desired state is even (it is zero). By lemma 4 the desired state can not 
            be reached by the initial state using legal moves.

10.-- Strong induction axiom--:
    Let P(n) be the predicate, If P(0) is true, and for every n (P(0)^P(1)^...^P(n)) => P(n+1) is true, for every n P(n) is true.

    [ATTENTION]
    Using strong induction, we can assume more, we can assume p(0), P(1), ... P(n) is true. So, it is much easier to use it.
    
    example: All strategies for the n-block game (split n block, gets point by product of split), produce the same score S(n)

    P(n): All strategies for the n-block game, produce the same score S(n)

    Base case: n=1 => S(1) = 0

    inductive step: Assume P(1), P(2), ... P(n) to prove P(n+1)

    look at n+1 blocks          n+1

                            k       n+1-k               1<=k<=n
            
            total score = k(n+1-k) + P(k) + P(n+1-k)        the last two terms came from strong induction

            we can't say that s(n+1) does not depends on k, so we get stuck, so we change the induction theorem:

            new P(n): All strategies for n-block game, produce the same score S(n) = n(n-1)/2

            total score = k(n+1-k) + k(k-1)/2 + (n+1-k)(n-k)/2 = n(n+1)/2 = S(n+1)

11. -- Number theory--: It is the study of --integers--.

[DEFINITION]
12. m | a  (m divides a)        If and only if, exists k (integer) that a = m * k

13. Problem: 

    a. We have a gallon jug (a = 3)
    b. We have b gallon jug (b = 5)
    c. a <= b

    --thm--: m | a and m | b , then m | any result from pouring, emptying and filing the jugs
    Or gcd(a, b) | any result from pouring, emptying, and filling the jugs
    (for example if one jug is 3 gallon and another is 6 gallon, you can not fill 4 gallon in the 6 gallon jug)

    State machine to prove the theorem:
    state pairs: (x, y)     x: # gallons in the a jug      y: # gallons in the b jug
    start state: (0, 0) 

    Transitions:
    
        a. emptying:
        (x, y) -> (0, y)
        (x, y) -> (x, 0)

        b. filling
        (x, y) -> (a, y)
        (x, y) -> (x, b)

        c. pouring
        (x, y) -> (0, x+y)    if x+y <= b
        (x, y) -> (x - (b - y), b) = (x+y-b, b)    if x+y >=b
        (x, y) -> (x + y, 0)          if x+y <=a
        (x, y) -> (a, y - (a - x)) = (a, y+x-a)    if x+y >= a

    -- Proof by induction 
        assume m | a and m | b

        invariant: P(n): If (x, y) is the state after n transitions, then m | x and m | y

        base case: (0, 0)       m | 0 and m | 0

        Induction step: Assume P(n)

        P(n + 1) is after another transition, 

        emptying is checked
        filling is checked 
        by axiom that m | linear of a and b         So, pouring is checked

[DEFINITION]
14.  gcd (a, b) =  -- greatest common divisor--

[DEFINITION]
15. a and b are --relatively prime-- if the gcd(a, b) = 1

16. thm: any linear combination L = sa + tb and 0 <= L <= b can be reached  (a jug and b jug)

    Proof: In order to proof this thm, we need that s > 0, so we can rewrite this linear combination:

        L = (s + mb)a + (t - ma)b   we can select m in a way that s + mb > 0

        L = s`a + t`b

    We are introducing --the algorithm that can produce  0 < L < b (the boundary situations is obvious)

    --Algorithm--: To obtain L gallons, we are going to repeat s` times the following algorithm:

        a. Fill the a jug

        b. pour into the b jug, when it becomes full, empty it out and continue pouring until a jug is empty 
    

        --proof of algorithm:

            Filled the a jug s` times
            Suppose that b jug is emptied u times
            Let r be the remainder in the b jug

            What we know:  0 <= r <= b   and  0 < L < b 
                r = s`.a - u.b          and L = s`a + t`b

                r = s`.a + t`b - t`b - u.b 
                r = L - (t` + u)b
            
            if t`+u is not zero r would be the out of range of 0 <= r <= b

17. Euclid's algorithm (The Pulverizer):
    
    --thm: There exists uniq q (quotient) and r (remainder) such that b = qa + r     0 <= r < a

    --lemma--: gcd(a,b) = gcd(rem(b,a), a)      (This is the algorithm)

        m: is common divisor for a and b

        m | a and m | b  => m | b - qa => m | rem(b, a) and we know m | a 


        gcd(a,b) <= gcd(rem(b,a), a)

    
18. --thm--: The gcd(a,b) is a liner combination of a and b

    (gcd(a,b) = smallest positive linear combination of a and b)

    --Proof--:
        By induction: P(n): If Euclid's algorithm reaches the gcd(x,y) after n steps, x and y are linear combination of a and b
        and gcd(a, b) = gcd(x, y)

        P(0) is true

        
19. --Encryption--:

    beforehand: Keys are exchanged
    encryption:   m` = Ekeys(m)
    decryption:   m = Dkeys(m`)

20. --Turing-- was the first one that proposed to use --number theory-- in cryptography

    --Turing's code V1--: 

        victory
        m = 2209032015182513
        (v is the 22th letters in alphabet)
        (13 is added to make m prime number)

        before hand: exchange secret --prime K--
        Enc: m` = mk
        Dec: m = m`/k

        (It is not easy to find out what is m and k from m`)
        --(It is hard to factor a product of two large primes)--

    -- Problem--: If someone in the middle intercept the two messages: 

        m`1 = m1 * k
        m`2 = m2 * k 

        So gcd(m`1, m`2) = k        and I have the secret prime key 
    
    -- Turing's code V2--:

        beforehand: a public prime p, a secret prime k
        Enc: message as a number   m in {0, 1, ... , p - 1}
                m` = rem(mk, p)
    
    To find the way for decryption, first we need some definition:

    --Def 1--: a and b are --relatively prime-- --if and only if gcd(a, b) = 1--  or --if and only if there exist s,t  sa + tb = 1--

    --Def 2--: x is --congruent(hamnehesht)-- to y --modulo(peymane) n--:        x ≋ y (mod n) if and only if n | (x-y)
            example: 31 ≋ 16 (mod 5)
    
    --Def 3--: The multiplicative inverse of x modulo n is a number x^-1, in {0, 1, ..., n-1} such that x. x^-1 ≋ 1 (mod n)

        2*3 ≋ 1 (mod 5)

        2 ≋ 3^-1 (mod 5)

        3 ≋ 2^-1 (mod 5)

    [For your self, one of these three numbers in the congruent can always be the remainder of two others]
    [For your self, decryption attack means finding the private key]

        Decryption: 

        m` = rem(mk, p) ≋ mk (mod p)    p | (mk - mk - xp) => p | xp
        if k . k^-1 ≋ 1         (because sometimes it is not possible to find multiplicative inverse)
        => m` ≋ mk (mod p)
        => m`k^-1 ≋ m (mod p)
        
        => ap = m`k^-1 - m => m = m`k^-1 - ap  
        => --m = rem(m`k^-1, p)--   because m is {0,1,..., p-1}

        Problem of Turning v2 --(Known plain text attack)--:

        m and m` is known for a message: 

            m` ≋ mk (mod p)

            gcd(m, p) = 1 => sm + tp = 1 => tp = 1 - sm => p | (1 - sm) => sm ≋ 1 (mod p) => we can compute m^-1 for m (mod p)

            => m`m^-1 ≋ k (mod p) => I know k (mod p) => we can compute k^-1 (mod p) so we can decrypt any message


/************ This section is about RSA algorithm *************/

[Definition]
21. Euler's Totient function (Ø(n)): The number of positive integers not greater than n that are relatively prime to it.

    example: 12 -> it is 1, 5, 7, 11 -> Ø(12) = 4
    example: 15 -> it is 1, 2, 4, 7, 8, 11, 13, 14 -> Ø(15) = 8

22. Euler's theorem: if gcd(n, k) = 1 or n and k are relatively prime => k^Ø(n) ≋ 1 (mod n)

    lemma 1: if gcd(n, k) = 1 then ak ≋ bk (mod n)  => a ≋ b (mod n)

        proof: gcd(n, k) = 1 => sn + tk = 1 => n | (1 - tk) => tk ≋ 1  (mod n)  => t = k^-1 (mod n) => akk^-1 ≋ bkk^-1 (mod n) => a ≋ b (mod n)
    
    lemma 2: Suppose that gcd(n, k) = 1
        let k1, ..., kr integers in {1, 2, 3, ..., n - 1} that are relatively prime to n (r = Ø(n)) 

        we can show X = {rem(k1.k, n), ..., rem(kr.k, n)} = {k1, k2, ..., kr} 

        Part 1: X has r elements

            assume rem(ki.k, n) = rem(kj.k, n) => kik ≋ kjk (mod n) => based on lemma 1: ki ≋ kj (mod n) => n | (ki - kj) 
            => because ki and kj are in {1, 2, 3, ..., n - 1} and they are smaller than n => ki - kj = 0 => ki = kj

        Part 2: X ⊆ {k1, k2, ..., kr}

            based on Euclid's algorithm: gcd(n, ki.k) = gcd(n, rem(ki.k, n)) = 1 => rem(ki.k, n) must be in {k1, ... , kr} => X ⊆ {k1, ... , kr}
    
    Euler's proof: 

        k1. k2. ... kr = rem(k1.k, n). rem(k2.k, n). ... rem(kr.k, n) ≋ k1.k . k2.k . ... kr.k (mod n)
        
        =>k1.k2. ... .kr ≋ k1.k2. ... .kr k^Ø(n) (mod n)
        based on gcd(k1.k2. ... .kr, n) = 1 and lemma 1 => k^Ø(n) ≋ 1 (mod n)

23. Fermat's little theorem: Suppose p is prime and k is in {1, 2, ... , p - 1} then k^(p-1) ≋ 1 (mod p)

    We can use this theorem to calculate the multiplicative inverse of k:

        k.k^(p-2) = k^(p-1) ≋ 1 (mod p) so k^(p-2) is the multiplicative inverse of k (mod p) => k

24. RSA algorithm: 
    
    --Beforehand--: A receiver creates a public and secret key and publish the public key, so anybody can encrypt the message using the public key

        1. Generate two distinct primes p and q
        2. let n = p.q
        3. Select integer e such that gcd(e, (p-1)(q-1)) = 1 /// The public key is the pair (e,n)
        4. Compute d such that d.e ≋ 1 (mod (p-1)(q-1))      /// The secret key is the pair (d,n)
        5. m is in the range (0, 1, ..., n-1)
    --Encryption--:
        m` = rem(m^e, n)
    
    --Decryption--:

        m = rem(m`^d, n)

        --Proof--:

            m` = rem(m^e,n) ≋ m^e (mod n)

            m` ≋ m^e (mod n) => m`^d ≋ m^(e.d) (mod n)

            There exist an integer (r) that (using d.e ≋ 1 (mod (p-1)(q-1))): ed = 1 + r (p-1)(q-1)

            => m`^d ≋ m . m ^(r (p-1)(q-1))  (mod n)

                => m`^d ≋ m . m ^(r (p-1)(q-1)) (mod p) and m`^d ≋ m . m ^(r (p-1)(q-1)) (mod q)


            Using Fermat's little theorem :

                m^(p-1) ≋ 1 (mod p)
                m^(q-1) ≋ 1 (mod q)

                => m`^d ≋ m (mod p) => p | (m`^d - m)       => n | (m`^d - m) => m = rem(m`^d, n)
                => m`^d ≋ m (mod q) => q | (m`^d - m)

//////////////////////// Graph theory /////////////////////////

25. Beginning the graph theory definitions:

Def: 
    A graph G is a pair of sets (V,E) where:
        V is a --none empty-- set of items called --Vertices or nodes--
        E is a set of 2-items subsets of V called --Edges--

Def: Two nodes xi and xj are --adjacent-- if {xi, xj} are in the E

Def: an edge e = {xi, xj} is --incident-- to xi and xj

Def: The number of edges incident to a node is the --degree of the node--

Def: --Simple graph--, the graph is simple if it has no --loop-- or --multiple edges--

26. Problem: Opposite genders

    graph: 

    nodes:

    men             women

    |V| = 300 M (The population of US)
    |Vm| = 147.6 M (The population of men in US)
    |Vw| = 152.4 M (The population of women in US)
    |E| = ??

    problem: ratio of average degree of men to average degree of women = Am / Aw

    Am = average degree of opposite-gender partners for men
    Aw = average degree of opposite-gender partners for women

    Am = Sum(deg(x)) x is in Vm / |Vm| = |E| / |Vm|
    Aw = Sum(deg(x)) x is in Vw / |Vw| = |E| / |Vw|

    Am / Aw = |Vw| / |Vm| = 152.4 / 147.6 = 1.0325

27. Graph --coloring problem--: 

    assign a color to each node so adjacent nodes get different colors.

    Def: The minimum value of K for which such a coloring exists -- Chromatic number --.

    --This is NP complete problem and can not find a solution for this--

    
    a. --Basic coloring algorithm-- for G = (V, E)

            1. Order the nodes v1, v2, ..., vn (Different ordering gives different results)

            2. Order the colors c1, c2, ..., 

            3. For i = 1, ..., n
                    Assign the lowest legal color to vi 
            
    [ATTENTION]
    This algorithms called --greedy algorithm--. You just think about one step at the time and move forward.

        --thm--: If every node in G has degree <=d, the basic algorithm uses at most d + 1 color for G.

            proof by induction: 

                induction hypothesis: If every node in n node graph G has degree <=d, the basic algorithm uses at most d + 1 color for G.

                Base case: n = 1 => 0 edges => degree = 0 => 1 color is work    => 1 color < d + 1

                Inductive step: Assume P(n) is true for the induction 

                    Let G (V, E) be any (n+1) graph node where d is the max degree
                
                Next step: 
                    Order the nodes: V1, .. ,Vn, Vn+1

                    new graph: V1, V2, ... Vn (The max degree is d)

                    Basic algorithm uses d + 1 color for new graph

                    Just color the detached node (because it has max d edges we can use the left color)

28. --Definition--: A graph G = (V,E) called --bipartite-- if V can be split into VL and VR so that all the edges connect a node in 
    VL to a node in VR


29. --Definition--: Given graph G = (V, E) a --matching-- is a subgraph of G where every node has a degree of 1.

30. --Definition--: A matching is --perfect-- if it has size |V|/2 (All the nodes are in the matching)

31. --Definition--: The --weight-- of a matching M is the sum of the weights on the edges in the M.

32. --Definition--: A --min-weight matching-- for G is a perfect matching for G with the minimum weight.

33. --Usually-- when we talk of weighted matching, we talk about the perfect matching.

34. Finding a min-weight or max-weight perfect matching is not a NP complete problem. However, it is really difficult to solve them.
    
    [ATTENTION]
    We solve another problem that every node has a --preferences--.

35. --Definition--: Given a matching M, x and y form a --rogue-- couple if they prefer each other over their mate.

36. --Definition--: A matching is --stable-- if there are no rogue couple.

37. --Stable marriage problem--:

        - There are N boys and N girls
        - Each boy has his own ranked list of all the girls 
        - Each girl has her own ranked list of all the boys 
    
    The goal is to find a perfect matching without rogue couples.

    -- Small example: 

    C,B,E,A,D     boy 1           girl A   3,5,2,1,4
    A,B,E,C,D     boy 2           girl B   5,2,1,4,3
    D,C,B,A,E     boy 3           girl C   4,3,5,1,2
    A,C,D,B,E     boy 4           girl D   1,2,3,4,5
    A,B,D,E,C     boy 5           girl E   2,3,4,1,5


    greedy algorithm: 

            boy 1 -> girl C
            boy 2 -> girl A 
            boy 3 -> girl D 
            boy 4 -> girl B    (boy 4 -> girl C is rogue couple) The greedy algorithm does not work
            boy 5 -> girl E     
    
    -- Mating algorithm--:

        - It takes place over several days
        - In the morning each girl comes to the balcony
        - Each boy go to the balcony of his favorite girl that has not been crossed out (If the boy has no girl in the list, that's done)
        - In the afternoon, the girls who have at least one suitors, looks all the suitors, pick the favorite and says come back tomorrow
            maybe I marry you 
        - all other boys cross the girl out of their lists 
        - In the night every boy who heard no, cross the girl out of their list 
        - The one who heard maybe I marry you, goes to the same girl's balcony
        - If we ever encounter the day, where every girl has one suitor, we will stop the algorithm.
    
        girls       Day 1       Day 2       Day 3       Day 4 
        A           2,4,5       5           5           5
        B           -           2           2, 1        2
        C           1           1,4         4           4 
        D           3           3           3           3 
        E           -           -           -           1   

                                --Cross off--
        Boys 
        1                       C           B
        2           A 
        3 
        4           A  
        5

        -- Proof that it always create stable matching

            We need to show: 

                a. The algorithm terminates (& quick)
                b. Every one gets married 
                c. No rouge couple
                d. Fairness (Is it good for boys or girls)
            

            -- Proof of a (The algorithm will be terminate in <= N^2 + 1): 

                Thm 1: TMA terminates in <= N^2 + 1 days 

                proof by contradiction: 
                    Suppose TMA does not terminate in N^2+1

                    Claim: if we don't terminate on a day, then some boy crosses a girl of his list. So, each day at least one girl will be crossed out
                        of the list.

                        N list with N names on them => <= N^2 crossed out so that is the contradiction
                    
            
            -- proof of b: 
                let p (invariant) = "If a girl G ever rejected a boy B, then G has a suitor who she prefers to B"

                Lemma 1: P is an invariant for TML

                proof by induction: 

                    Base case: day 0, no one is rejected yet, so it is true

                    Induction step: Assume P holds at day of d 

                        Case 1: G reject B at day d+1, Then there was someone better => P it true at d+1
                        Cast 2: G reject B before d+1, G had a better suitor at day d => 

                Thm 2: Everyone is married in TMA:

                    Proof by contradiction: We assume that some boy B is not married. 

                    This means B was rejected by every girl, By lemma 1, it means every girl has a better suitor. That means every girl is married. 
                    That means every boy got married. So, it is contradiction.  
            

            -- proof of c: 

                 