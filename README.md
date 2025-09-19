These files contain (most) everything to do with the SageMath code implementing the Lattice Reconstitution Attack against the HPPK KEM, and two variants of the Merkle-Hellman PKC
(named Unshuffled and Shuffled).

In general, there are individual and mass testing variants of all LRA algorithms.
For specific running procedures after loading the given files:

lra-hppk.sage: 
    You can generate a private/public HPPK key-pair using, e.g., 'k=skpkgen()' and then run 'LRA(k[1])' to execute LRA-HPPK 
    on the public key, 'k[1]', observing that the return is, as far as tested, invariably 'k[0]'.
    Whereas, running 'LRAMass(n)' will run the LRA 'n' times and compute averages of various datas.

lra-mhs.sage: 
    Similarly, you can execute 'k=kMHU(n)' for an -unshuffled- key of length 'n', then run, e.g., 'LRAMHS(k[0],6,True)' to execute LRA-MHS 
    on the public key, 'k[0]' with discriminator matrix reduction of dimension 6. Choosing 'True' returns the equivalent secret key as primary output.
    Likewise, 'MerkSLRAMass(ntests,n,d)' will collect data from running 'ntests' on the Shuffled MH PKC of key-length 'n' with discriminator construction
    of dimension 'd'. N.B.: Shuffled keys are -not- presently supported, though our LRA functions use fully random coefficient draws wherever significant. 
    The difference is almost purely in presentation, and we've left it as such for clarity of programming and study; there are only negligible additions to 
    memory and computation upon adding the necessary sorting and book-keeping functions for including the absentee permutation for a full, equivalent 
    shuffled Merkle-Hellman private key. You can use the function 'pkeqMH(pk,esk)' to check the effectiveness of a demonstrated equivalent key 'esk' at decrypting
    a randomly generated ciphertext as encrypted via public (unshuffled) key 'pk'.

lra-mhu.sage: 
    Generally, as with lra-mhs.sage, execute 'k=kMHU(n)' and, e.g., 'LRAMHU(k[0],6,True)' for single execution, or 'MerkULRAMass(ntests,n,d)' for mass testing.
    
wlra.sage:
    Everything to do with the Weak Lattice Reconstitution Attack. Once again, you can run 'k=skpkgen()' and then 'WLRA(k[1],True)' to run the WLRA on
    the given HPPK public key, 'k[1]' to output the private key (assuming you have time to do it, this algorithm is indeed worse than the LRA). Setting 'True' 
    gives a more detailed ouput process. Likewise, 'WLRAMass(rounds,False)' will run this algorithm 'rounds' many times, then give you cumulative data as to
    the algorithm's general success and internal complexity; using 'False' gives a more reasonably compact output.
    For the WLRA simulator, you can also execute 'k=skMgen()' to generate an HPPK half-key and then 'WLRASim(k[0])' to see if the WLRA would essentially work 
    (and fully, if you included another half-key), albeit much faster. Lastly, 'WLRASimMass(rounds)' will run WLRASim 'rounds' many times on randomly generated keys
    and collect relevant statistical data.
    
