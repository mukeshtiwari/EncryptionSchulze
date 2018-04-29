package schulze;


import java.math.BigInteger;
import java.text.DateFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.Arrays;

import ch.bfh.unicrypt.UniCryptException;
import ch.bfh.unicrypt.crypto.mixer.classes.IdentityMixer;
import ch.bfh.unicrypt.crypto.mixer.classes.ReEncryptionMixer;
import ch.bfh.unicrypt.crypto.proofsystem.challengegenerator.classes.FiatShamirSigmaChallengeGenerator;
import ch.bfh.unicrypt.crypto.proofsystem.challengegenerator.interfaces.SigmaChallengeGenerator;
import ch.bfh.unicrypt.crypto.proofsystem.classes.EqualityPreimageProofSystem;
import ch.bfh.unicrypt.crypto.proofsystem.classes.PermutationCommitmentProofSystem;
import ch.bfh.unicrypt.crypto.proofsystem.classes.ReEncryptionShuffleProofSystem;
import ch.bfh.unicrypt.crypto.schemes.commitment.classes.PermutationCommitmentScheme;
import ch.bfh.unicrypt.crypto.schemes.encryption.classes.ElGamalEncryptionScheme;
import ch.bfh.unicrypt.helper.math.Permutation;
import ch.bfh.unicrypt.helper.prime.SafePrime;
import ch.bfh.unicrypt.helper.random.deterministic.DeterministicRandomByteSequence;
import ch.bfh.unicrypt.math.algebra.dualistic.classes.ZModElement;
import ch.bfh.unicrypt.math.algebra.general.classes.Pair;
import ch.bfh.unicrypt.math.algebra.general.classes.PermutationElement;
import ch.bfh.unicrypt.math.algebra.general.classes.PermutationGroup;
import ch.bfh.unicrypt.math.algebra.general.classes.ProductGroup;
import ch.bfh.unicrypt.math.algebra.general.classes.Triple;
import ch.bfh.unicrypt.math.algebra.general.classes.Tuple;
import ch.bfh.unicrypt.math.algebra.general.interfaces.CyclicGroup;
import ch.bfh.unicrypt.math.algebra.general.interfaces.Element;
import ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModElement;
import ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModPrime;
import ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModSafePrime;
import ch.bfh.unicrypt.math.function.classes.GeneratorFunction;
import ch.bfh.unicrypt.math.function.classes.PowerFunction;
import ch.bfh.unicrypt.math.function.interfaces.Function;
import ch.bfh.unicrypt.crypto.encoder.classes.ZModPrimeToGStarModSafePrime;
import ch.bfh.unicrypt.crypto.keygenerator.interfaces.KeyPairGenerator;

public class HelloWorld {
	
	//Simplification of java for OCaml
	
	//Begin data structures
	
	private static class ElGamalCiphertext {	//An ElGamal Ciphertext is represented as two BigIntegers
		public ElGamalCiphertext(BigInteger c1, BigInteger c2){
			this.c1 = c1;
			this.c2 = c2;
		}
		
		public ElGamalCiphertext(Pair c){
			this.c1 = c.getFirst().convertToBigInteger();
			this.c2 = c.getSecond().convertToBigInteger();
		}
		
		
		public BigInteger c1;
		public BigInteger c2;
	}
	
	private static class EncPrefrence {	//An encrypted preference denotes that a candidate
		// is preferred over another, denoted preferred and over respectively, the ciphertext contains
		//encryption of the weight of this preference
		public EncPrefrence( ElGamalCiphertext ciphertext) {
			this.ciphertext = ciphertext;
		}
		 public ElGamalCiphertext ciphertext;
	}
	
	private static class EncPrefrenceWithZKP {	//An encrypted preference denotes that a candidate
		// is preferred over another, denoted preferred and over respectively, the ciphertext contains
		//encryption of the weight of this preference
		public EncPrefrenceWithZKP( ElGamalCiphertext ciphertext) {
			this.ciphertext = ciphertext;
		}
		 public ElGamalCiphertext ciphertext;
		 public String ZKP;
	}
	
	private static class Prefrence { //A preference denotes that a candidate
		// is preferred over another, denoted preferred and over respectively, the plaintext contains
		//the weight of this preference
		public Prefrence(BigInteger plaintext) {
			 this.plaintext = plaintext;
		}
		public BigInteger plaintext;
	}
	
	private static class PrefrenceWithZKP { //A preference denotes that a candidate
		// is preferred over another, denoted preferred and over respectively, the plaintext contains
		//the weight of this preference
		public PrefrenceWithZKP(BigInteger plaintext, String ZKP) {
			 this.plaintext = plaintext;
			 this.ZKP = ZKP;
		}
		public BigInteger plaintext;
		public String ZKP;
	}

	private static class EncBallot { //An encrypted ballot contains a list of encrypted preferences
		// it is expected that this list will be of length n^2 containing the preference relationship between
		// each candidate the all n candidates
		// TODO check that the EncPrefrence is correctly formed
		public EncBallot(List<EncPrefrence> prefrences) {
			this.prefrences = prefrences;
		}
		
		public List<EncPrefrence> prefrences;
	}
	
	private static class EncBallotWithZKP { //An encrypted ballot contains a list of encrypted preferences
		// it is expected that this list will be of length n^2 containing the preference relationship between
		// each candidate the all n candidates
		// TODO check that the EncPrefrence is correctly formed
		public EncBallotWithZKP(List<EncPrefrenceWithZKP> prefrences) {
			this.prefrences = prefrences;
		}
		
		public List<EncPrefrenceWithZKP> prefrences;
	}
	
	private static class Ballot { //A ballot contains a list of preferences
		// it is expected that this list will be of length n^2 containing the preference relationship between
		// each candidate the all n candidates
		// TODO check that the preferences is correctly formed
		public Ballot(List<Prefrence> prefrences) {
			this.prefrences = prefrences;
		}
		
		public List<Prefrence> prefrences;
	}
	 
	private static class BallotWithZKP {//A ballot contains a list of preferences
		// it is expected that this list will be of length n^2 containing the preference relationship between
		// each candidate the all n candidates each preference contains a proof that is correctly decryted
		// TODO check that the preferences is correctly formed
		public BallotWithZKP(List<PrefrenceWithZKP> prefrences) {
			this.prefrences = prefrences;
		}
		
		public List<PrefrenceWithZKP> prefrences;
	}
	
	//End Data structures 
	
	@SuppressWarnings("unchecked")
	public static BigInteger generateSK() {  // Generates a secret key
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		KeyPairGenerator kpg = elGamal.getKeyPairGenerator();
		Element<BigInteger> privateKey = kpg.generatePrivateKey();
		return privateKey.convertToBigInteger();
	}
	
	@SuppressWarnings("unchecked")
	public static BigInteger generatePK(BigInteger privateKey) { //Generates a public key from a secret key
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		KeyPairGenerator kpg = elGamal.getKeyPairGenerator();
		Element<BigInteger> publicKey = kpg.generatePublicKey(group.getElement(privateKey));
		return publicKey.convertToBigInteger();
	}
	
	public static EncBallot EncBallotMulti(EncBallot b1, EncBallot b2) { //Takes two encrypted ballots
		//and produces a new encrypted ballot by pairwise multiplication of ciphertexts
		//TODO There are no checks to make sure such multiplication is possible
		return new EncBallot(
			IntStream.range(0, b1.prefrences.size()).mapToObj( //For all preferences
			i -> new EncPrefrence(multiplyCiphertext(b1.prefrences.get(i).ciphertext,b2.prefrences.get(i).ciphertext)) //Multiply the ciphertexts
			).collect(Collectors.toList())
		);
	}
	
	//This function calculates the discrete log of element to the base generator 
	//TODO the function will run in infinite time if no log exists, there should be some limit imposed
	//TODO the function will run in nearly infinite time if the log is sufficently larger, some limit should be imposed
	private static BigInteger dLog(GStarModElement generator, Element<BigInteger> element) {
		return BigInteger.valueOf(IntStream.iterate(0, i -> i++).filter(i -> generator.power(i).equals(element)).findFirst().getAsInt());
	}
	
	//This function takes two BigIntegers representing group elements and produces their product in the group
	public static BigInteger groupOp(BigInteger element1, BigInteger element2) throws UniCryptException {
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement one = group.getElementFrom(element1);
		GStarModElement two = group.getElementFrom(element1);
		return one.multiply(two).getValue();
	}
	
	//This function takes two ElGamal ciphertexts and produces their product
	public static ElGamalCiphertext multiplyCiphertext(ElGamalCiphertext c1, ElGamalCiphertext c2) {
		try {
			return new ElGamalCiphertext(groupOp(c1.c1, c2.c1), groupOp(c1.c2, c2.c2));
		} catch(Exception exp) {
			return new ElGamalCiphertext(BigInteger.ZERO, BigInteger.ZERO);
		}
	}
	
	//This function converts an ElGamal BigInteger ciphertext to unicrypt encoding
	public static Tuple ciphertextConvBItT(ElGamalEncryptionScheme elGamal, ElGamalCiphertext c) {
		try {
			return elGamal.getEncryptionSpace().getElementFrom(c.c1, c.c2);
		} catch (UniCryptException e) {
			//TODO we fail silently (to make the lamdas happy), we shouldn't
			e.printStackTrace();
			return elGamal.encrypt(elGamal.getGenerator(), elGamal.getGenerator());//Not sure if this even makes sense
		}
	}
	
	//This function takes an encrypted ballot and the private key and returns a (decrypted) ballot
	@SuppressWarnings("unchecked")
	public static Ballot decBallot(EncBallot b, BigInteger privateKey) {
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		Element<BigInteger> privateKeyElem = group.getZModOrder().getElement(privateKey);
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		return new Ballot(b.prefrences.stream().map(i -> 
			new Prefrence(dLog(generator, elGamal.decrypt(privateKeyElem, ciphertextConvBItT(elGamal, i.ciphertext)))
		)).collect(Collectors.toList()));
	}
	
	//This function takes an encrypted ballot and the private key and returns a (decrypted) ballot
	// it also returns a ZKP of the correct of decryption
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public static BallotWithZKP decBallotZKP(EncBallot b, BigInteger privateKey) {
		//Setup ElGamal
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		Element<BigInteger> privateKeyElem = group.getZModOrder().getElement(privateKey);
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		
		//Setup ZKP
		// Create proof functions
		Function f1  = PowerFunction.getInstance(group);
		EqualityPreimageProofSystem equalityPreimageProofSystem = EqualityPreimageProofSystem.getInstance(f1);
		
		//Return
		return new BallotWithZKP(b.prefrences.stream().map(i -> {
			Tuple c = ciphertextConvBItT(elGamal, i.ciphertext);
			Element encodedMessage =  elGamal.decrypt(privateKeyElem, c);
			GStarModElement partialDecryption = (GStarModElement) c.getLast();
			Pair publicInput = Pair.getInstance(group.power(generator, privateKeyElem), partialDecryption);
			//equalityPreimageProofSystem.generate(privateKeyElem, publicInput)   //Generate (private input and public input
			return new PrefrenceWithZKP(dLog(generator, encodedMessage),equalityPreimageProofSystem.generate(privateKeyElem, publicInput).toString());
			}
		).collect(Collectors.toList()));
	}

	//TODO
	public static EncBallot encBallot(Ballot b, BigInteger publicKey)
	{
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		Element<BigInteger> publicKeyElem = group.getElement(publicKey);
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		
		return new EncBallot(b.prefrences.stream().map(i -> new EncPrefrence(
				new ElGamalCiphertext(elGamal.encrypt(publicKeyElem, generator.power(i.plaintext)))
				)).collect(Collectors.toList()));
		}
	
//	//TODO
//	public static EncBallotWithZKP EncBallotZKP(Ballot b, BigInteger publicKey)
//	{
//		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
//		GStarModElement generator = group.getDefaultGenerator();
//		Element<BigInteger> publicKeyElem = group.getElement(publicKey);
//		ElGamalEncryptionScheme elGamal = 
//				ElGamalEncryptionScheme.getInstance(generator);
//		
//		return new EncBallotWithZKP(b.prefrences.stream().map(i -> {
//				return new EncPrefrenceWithZKP(new ElGamalCiphertext(elGamal.encrypt(publicKeyElem, generator.power(i.plaintext),)),);
//				).collect(Collectors.toList()));
//	}
//	
//	//TODO
//		public static EncBallotZKPOfPlaintext(Ballot b, BigInteger publicKey)
//		{
//			GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
//			GStarModElement generator = group.getDefaultGenerator();
//			Element<BigInteger> publicKeyElem = group.getElement(publicKey);
//			ElGamalEncryptionScheme elGamal = 
//					ElGamalEncryptionScheme.getInstance(generator);
//			ElGamalEncryptionValidityProofSystem getInstance
//			return new EncBallot(b.prefrences.stream().map(i -> new EncPrefrence(i.prefered, i.over, 
//					new ElGamalCiphertext(elGamal.encrypt(publicKeyElem, generator.power(i.plaintext)))
//					)).collect(Collectors.toList()));
//		}
		
	//Todo
	//Row Permute with ZKP
		
	//Todo
	//Column Permute with ZKP
		
		// This function takes Array of BigIntegers from OCaml code and returns 
		// plainttext. Assuming that we have two candidates, our Array b would of size 4 (n X n for candidate size n and will be interpreted as matrix )
		public static Ballot constructBallot(BigInteger[] b)
		{

			return new Ballot(Arrays.asList(b).stream().map(i -> new Prefrence(i)).collect(Collectors.toList()));
			/*
			List<Prefrence> bal = new ArrayList();
			for (int i = 0; i < b.length; i++)
			{
				bal.add(new Prefrence (b[i]));
			}
			return new Ballot(bal); */
		}

		// This function is same as old one (n X n) matrix, but values are taken in pair (i, i + 1)
		// Try to change this funciton into lambda function
		public static EncBallot constructEncBallot (BigInteger[] b)
		{

			List<EncPrefrence> encbal = new ArrayList();
			for(int i = 0; i < b.length; i+= 2)
			{ 
				encbal.add(new EncPrefrence(new ElGamalCiphertext(b[i], b[i+1])));
			}
			return new EncBallot(encbal);
		}

		// This function converts ballots back to list of BigInteger
		public static BigInteger[] destructBallot(Ballot b)
		{
			List<Prefrence> t = b.prefrences;
			int len = t.size();
			BigInteger[] bal = new BigInteger[len];
			for(int i = 0 ; i < len; i++) 
				bal[i] = t.get(i).plaintext;
			return bal;
		}


		// Converts Encrypted ballot into Array of BigInteger
		public static BigInteger[] destructEncBallot(EncBallot b)
		{
			List<EncPrefrence> t = b.prefrences;
			int len = t.size();
			BigInteger[] bal = new BigInteger [2*len];
			for(int i = 0, j = 0; i < len; i++, j += 2)
			{
				bal[j] = t.get(i).ciphertext.c1;
				bal[j+1] = t.get(i).ciphertext.c2;
			}
			return bal;
		}

		public static BigInteger add_for(BigInteger n, BigInteger m)
		{
			return n.add(m);
		}
	
	public static void main(String[] args) throws UniCryptException {
		
		
		
		// Write Public key and Private Key in file. For testing purpose, make private key 1 and public key generator
		// We Start from OCaml main function and read a Encrypted ballot, Convert it in Java Array (EncBallot data structure) 
		// and call multiplyBallot. Takes the EncBallot and convert it to OCaml Array 
		// 
		
		ElGamalCiphertext c = new ElGamalCiphertext(BigInteger.ONE, BigInteger.ONE);
		
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		Element generator = group.getDefaultGenerator();
		System.out.println(group.getModulus());
		System.out.println(generator);
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		KeyPairGenerator kpg = elGamal.getKeyPairGenerator();
		Element<BigInteger> privateKey = kpg.generatePrivateKey();
		Element<BigInteger> publicKey = kpg.generatePublicKey(privateKey);
		System.out.println(privateKey);
		System.out.println(publicKey);
		
		Element<BigInteger> cc = group.power(generator, 1); //g^m
		System.out.println(cc);
		Pair ciphertext = elGamal.encrypt(publicKey, cc);
		System.out.println(ciphertext);
		Element plaintext = elGamal.decrypt(privateKey, ciphertext);
		System.out.println(plaintext);
		
		
		
		
		//Element privateKey = (Element) BigInteger.ONE;
		//Element publicKey = generator;
		
		
		//System.out.println(group);
		//System.out.println(group.getOrder());
		//System.out.println(group.getDefaultGenerator().getValue());
		//ElGamalEncryptionScheme elGamal = ElGamalEncryptionScheme.getInstance(group);
		
		
		/*
		// size of vectors that are being permuted.
		int n = 4;
		long startTime = System.nanoTime();
		
		// set up crypto system
		CyclicGroup group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		ElGamalEncryptionScheme elGamal = ElGamalEncryptionScheme.getInstance(group.getDefaultGenerator());
		
		
		Element pk = group.getRandomElement();
		
	
		// generate random permutation and shuffle
		ReEncryptionMixer mixer = ReEncryptionMixer.getInstance(elGamal, pk, n);
		PermutationElement pi = mixer . getPermutationGroup ( ) . getRandomElement ( ) ;

		// generate shuffle proof system
		ReEncryptionShuffleProofSystem rsps =
				ReEncryptionShuffleProofSystem.getInstance(n, elGamal, pk);

		

		// generate permutation commitment scheme and proof
		// general init
		PermutationCommitmentScheme pcs =
				PermutationCommitmentScheme.getInstance(group, n);
		PermutationCommitmentProofSystem pcps =
				PermutationCommitmentProofSystem . getInstance ( group , n ) ;
        // s is the randomness used to generate the commitment
		Tuple s = pcs . getRandomizationSpace() . getRandomElement() ;
		// c_pi is a commitment to a permutation pi
		Tuple c_pi = pcs . commit (pi , s) ;
        // offlinePrivateInput is used to generate the offlineProof of commitment		
		Pair offlinePrivateInput = Pair . getInstance ( pi , s ) ;
		// offlinePublicInput is the commitment to the permutation pi
		Element offlinePublicInput = c_pi;
		// offlineProof shows that c_pi indeed commits to pi		
		Tuple offlineProof =  pcps. generate ( offlinePrivateInput ,offlinePublicInput ) ;
		
		long initDoneTime = System.nanoTime();
		System.out.print("Initialisation time: ");
		System.out.println(initDoneTime - startTime); 

		// this happens for each vector that is to be encrypted.
		// generate random vector of length n
		Tuple ciphertext = Tuple.getInstance();
		for (int i = 1; i <= n; i++)
		{
			Pair c = elGamal .   encrypt(pk, group.getRandomElement());
			ciphertext = ciphertext.add(c);
			
		}
		long ballotDoneTime = System.nanoTime();
		System.out.print("Time to create ballot: ");
		System.out.println(ballotDoneTime - initDoneTime); 
		
		// r is the randomness used in the shuffle
		Tuple r = mixer . generateRandomizations ( ) ;
		long randomDoneTime = System.nanoTime();
		System.out.print("Time to gnerate randomness for shuffle: ");
		System.out.println(randomDoneTime - ballotDoneTime); 
		
		//shuffle ciphertext
		Tuple shuffledCiphertext = mixer.shuffle(ciphertext, pi, r);
		
		long shuffleDoneTime = System.nanoTime();
		System.out.print("Time for one shuffle: ");
		System.out.println(shuffleDoneTime - ballotDoneTime);
		
		// create a proof of the fact that the shuffle above is indeed a shuffle by pi
		// onlinePublicInput is the object the correctness of which we want to verifu
		Triple onlinePublicInput =
				Triple . getInstance (c_pi , ciphertext , shuffledCiphertext) ;
		// onlinePrivateInput is needed to generate the proof
		Triple onlinePrivateInput = Triple . getInstance (pi , s , r) ;
		// generate online proof of correctness of shuffle
		Tuple onlineProof =
				rsps . generate ( onlinePrivateInput , onlinePublicInput );
		
		long proofDoneTime = System.nanoTime();
		System.out.print("Time to generate proof: ");
		System.out.println(proofDoneTime - shuffleDoneTime); 
		
        // start of verification			
		boolean v1 = pcps.verify(offlineProof, offlinePublicInput);
		boolean v2 = rsps.verify(onlineProof, onlinePublicInput);
		boolean v3 = offlinePublicInput . isEquivalent (onlinePublicInput . getFirst ());
		
		if( v1 && v2 && v3) System.out.println("Zero knowledge proof verified");
		long stopTime = System.nanoTime();
		System.out.print("Time to verify correctness:");
		System.out.println(stopTime - proofDoneTime); */
			
	} 

}

