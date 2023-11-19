clear;



mem := 80000000000; 
SetMemoryLimit(mem); // Set max memory


p := 101;
K := GF(p);
Z := IntegerRing();


t := 4; // Number of key variables
gs := t; // #Known/guessed variables
d := 3; // Exponent of S-box

rfstart := 1; // Full rounds start
rfend := 1;   // Full rounds end

rf := rfstart+rfend; // Total number of full rounds
rp := 7; // #Partial rounds
R_tot := rf+rp; // Total number of rounds


n := t*(rf)+rp; // Number variables in polynomialring of the ideal 

R := PolynomialRing(K,n,"grevlex"); // Polynomial ring over GF(p), n variables, with monomial order graded reverse lexicographic order


secure := false;

// Generate elements for matrix 
while secure eq false do

    // 2*t random distinct elements in GF(p)
    rand := [];
    sum := 0;
    while #rand eq 2*t eq false do
        randomInteger := Random(0, p-1);
        if randomInteger in rand eq false then
            rand := rand cat [randomInteger];
        end if;
    end while;


    // Split the elements in two sets
    A := rand[1..t];
    B := rand[t+1..2*t];

    // Elements in the two sets at any index should not equal zero when added together. 
    for i in [1..t] do
        for j in [1..t] do
            if (A[i] + B[j]) mod p eq 0 then
                sum := 1;
            end if;
        end for;
    end for;

    if sum eq 0 then 
        secure := true;
    end if;

end while;


// Make a Cauchy matrix by using the elements  
M := ZeroMatrix(K, t, t);
for i in [1..t] do
    for j in [1..t] do
        divi := (A[i]-B[j]) mod p;
        M[i,j] := 1/divi;
    end for;
end for;

MRing := ChangeRing(M,R);
Plain := RandomMatrix(K,t,1); // Random plaintext
Key := RandomMatrix(K,t,1);   // Random key



// Add key function
function AddKey(State,Key)
    return State + Key;
end function;

// Full s-box function
function FullSbox(State,d)

    for i in [1..NumberOfRows(State)] do
        State[i,1] := (State[i,1])^d;
    end for;
    
    return State;
end function;

// Partial s-box function
function PartialSbox(State,d)
    // S-Box only on the first element
    State[1,1] := (State[1,1])^d;
    return State;
end function;

// Multiply by permutation matrix
function MultM(State,M)
    return M*State;
end function;

// Encryption function of HadesMiMC
function HadesEnc(State,d,rounds,key)
    // First round
    r := rounds;

    // full rounds start
    for i in [1..rfstart] do
        State := MultM(FullSbox(AddKey(State,key),d),M);
    end for;

    // partial rounds
    for i in [rfstart+1..rfstart+rp] do
        State := MultM(PartialSbox(AddKey(State,key),d),M);
    end for;

    // rth round end
    for i in [rfstart+rp+1..r-1] do
        State := MultM(FullSbox(AddKey(State,key),d),M);
    end for;
    
    // last round
    State := AddKey(FullSbox(AddKey(State,key),d),key);
    return State;
end function;

// Inverse add key
function invAddKey(State,keyIn)
    return State-keyIn;
end function;

// Inverse full s-box
function invFullSbox(State,d)
    invD := Z!((2*p-1)/d);
    for i in [1..NumberOfRows(State)] do
        State[i,1] := State[i,1]^invD;
    end for;
    return State;	
end function; 

// Inverse partial s-box
function invPartialSbox(State,d)
    invD := Z!((2*p-1)/d);
    State[1,1] := (State[1,1])^invD;
    return State;
end function;

// Inverse permutation matrix multiplication
function invMultM(State,M)
    return (M^(-1))*State;
end function;

// Decryption function of HadesMiMC
function HadesDec(State,d,rounds,key)
    r := rounds;

    //irregular round
    State := invAddKey(invFullSbox(invAddKey(State,key),d),key);
    // full round
    for i in [2..rfend] do
        State := invAddKey(invFullSbox(invMultM(State,M),d),key);
    end for;

    // partial rounds
    for i in [rfstart+1..rfstart+rp] do
        State := invAddKey(invPartialSbox(invMultM(State,M),d),key);
    end for;

    // full rounds end
    for i in [rfstart+rp+1..r] do
        State := invAddKey(invFullSbox(invMultM(State,M),d),key);
    end for;
    
    return State;
end function;



enc := HadesEnc(Plain,d,R_tot,Key); // Encrypt random plaintext
dec := HadesDec(enc,d,R_tot,Key);   // Decrypt the encrypted plaintext
print(dec eq Plain);                // Check if decryption equals original plaintext


// Add polynomials in state to set of polynomials, and introduce new variables. Used for full rounds.
function addToIdeal(I,State,count)
    for i in [1..t] do 
        I := I cat [State[i,1]-R.count];
        State[i,1] := R.count;
        count := count+1;
    end for;
    return I,State,count;
end function;

// Generate polynomial set, and compute the Grobnes Basis using the F4 algorithm.
function SympHadesEnc(State,d,rounds,key,t,c,Keey)
    
    count := t+1; // Counter for variables
    ind := 1;     // Index of partial s-box
    
    // Ideal
    I := []; 

    r := rounds; // Total number of rounds
    
    // full rounds start
    for i in [1..rfstart] do
        State := FullSbox(AddKey(State,key),d);
        I,State,count := addToIdeal(I,State,count);
        State := MultM(State,MRing);
    end for;

    // partial rounds
    for i in [rfstart+1..rfstart+rp] do
        State := PartialSbox(AddKey(State,key),d);
        I := I cat [State[ind,1]-R.count];
        State[ind,1] := R.count;
        count := count+1;
        State := MultM(State,MRing);
    end for;

    // full rounds end. Note that rfend has to be greater than or equal to 2 in order for the code to enter this for loop
    // this is because last round does not include multiplication by permutation matrix
    for i in [rfstart+rp+1..r-1] do
        State := FullSbox(AddKey(State,key),d);
        I,State,count := addToIdeal(I,State,count);
        State := MultM(State,MRing);
    end for;
    // last round
    State := AddKey(State,key);
    State := FullSbox(State,d);
    
    c := ChangeRing(c,R);

    Cipher := AddKey(State,key);

    for i in [1..t] do 
        I := I cat [Cipher[i,1]-c[i,1]];
    end for;

    // key guessing
    for i in [1..gs] do 
        I := I cat [key[i,1]-Keey[i,1]];
    end for;
    
    // In order for us to be able to guess other variables than the key variables, we first compute the Groebner Basis of our polynomial ideal
    // Then we remove all linear equations, make a list of the guessed variables, and add them to our ideal.
    SetVerbose("Groebner", 0); 
    J := GroebnerBasis(I);
    I := I[1..#I-gs];
    guesses := [J[1],J[2]];
    I := I cat guesses;

    dest := "test/";
    dir := dest;
    
    // Write to file
    nxt := true;
    fileCounter := 1;
     
    while nxt eq true do 
        dir *:= IntegerToString(fileCounter);
        dir *:=".txt"; 
        dir;
        try
            f := Open(dir, "r");
            fileCounter +:= 1;
            dir := dest;
        catch e
            f := Open(dir, "w");
            fileCounter +:= 1;
            SetOutputFile(dir);
            print("t = " cat IntegerToString(t));
            print("rf = " cat IntegerToString(rf));
            print("rp = " cat IntegerToString(rp));
            print("n = " cat IntegerToString(n));
            print("d = " cat IntegerToString(d));
            print("Memory Limit = " cat IntegerToString(mem));
            print("Guessed = " cat IntegerToString(#guesses));
            
            dir := dest;
            nxt := false;
        end try;
    end while;
        
    SetVerbose("Groebner",2);	
    J := GroebnerBasis(I);
    J;    
    print "Experiment complete";
    return J; 
    
end function;

poly := ZeroMatrix(R, t, 1);

zeroPlain := ZeroMatrix(R, t, 1);


// Key variables
for i in [1..t] do
    poly[i,1] := R.i;
end for; 

ciphertext := HadesEnc(Plain,d,R_tot,Key);
SympHadesEnc(Plain,d,R_tot,poly,t,ciphertext,Key);
