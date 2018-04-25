package Schulze;


import java.math.BigInteger;
import java.text.DateFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;


import ch.bfh.unicrypt.UniCryptException;
import ch.bfh.unicrypt.crypto.mixer.classes.IdentityMixer;
import ch.bfh.unicrypt.crypto.mixer.classes.ReEncryptionMixer;
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
import ch.bfh.unicrypt.math.algebra.general.interfaces.Element;
import ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModSafePrime;
import ch.bfh.unicrypt.crypto.schemes.encryption.classes.ElGamalEncryptionScheme;
import ch.bfh.unicrypt.crypto.encoder.classes.ZModPrimeToGStarModSafePrime;
import ch.bfh.unicrypt.crypto.keygenerator.interfaces.KeyPairGenerator;

public class HelloWorld {
	
	//Simplification of java for OCaml
	
	private static class ElGamalCiphertext {
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
	
	private static class EncPrefrence {
		public EncPrefrence(String prefered, String over, ElGamalCiphertext ciphertext) {
			this.prefered = prefered;
			this.over = over;
			this.ciphertext = ciphertext;
		}
		public String prefered;
		public String over;
		public ElGamalCiphertext ciphertext;
	}
	
	private static class Prefrence {
		public Prefrence(String prefered, String over, BigInteger plaintext) {
			this.prefered = prefered;
			this.over = over;
			this.plaintext = plaintext;
		}
		public String prefered;
		public String over;
		public BigInteger plaintext;
	}

	private static class EncBallot {
		public EncBallot(List<EncPrefrence> prefrences) {
			this.prefrences = prefrences;
		}
		
		public List<EncPrefrence> prefrences;
	}
	
	private static class Ballot {
		public Ballot(List<Prefrence> prefrences) {
			this.prefrences = prefrences;
		}
		
		public List<Prefrence> prefrences;
	}
	
	private static BigInteger dLog(GStarModElement generator, Element<BigInteger> element) {
		return BigInteger.valueOf(IntStream.iterate(0, i -> i++).filter(i -> generator.power(i).equals(element)).findFirst().getAsInt());
	}
	
	public static BigInteger groupOp(BigInteger element1, BigInteger element2) throws UniCryptException {
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement one = group.getElementFrom(element1);
		GStarModElement two = group.getElementFrom(element1);
		return one.multiply(two).getValue();
	}
	
	public static ElGamalCiphertext multiplyCiphertext(ElGamalCiphertext c1, ElGamalCiphertext c2) {
		try {
			return new ElGamalCiphertext(groupOp(c1.c1, c2.c1), groupOp(c1.c2, c2.c2));
		} catch(Exception exp) {
			return new ElGamalCiphertext(BigInteger.ZERO, BigInteger.ZERO);
		}
	}
	
	public static Element ciphertextBigIntegerToElement(ElGamalEncryptionScheme elGamal, ElGamalCiphertext c) {
		try {
			return elGamal.getEncryptionSpace().getElementFrom(c.c1, c.c2);
		} catch (UniCryptException e) {
			e.printStackTrace();
			return elGamal.getGenerator();
		}
	}
	
	public static Ballot decBallot(EncBallot b, BigInteger privateKey) {
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		Element<BigInteger> privateKeyElem = group.getZModOrder().getElement(privateKey);
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		return new Ballot(b.prefrences.stream().map(i -> new Prefrence(i.prefered, i.over, 
			dLog(generator, elGamal.decrypt(privateKeyElem, ciphertextBigIntegerToElement(elGamal, i.ciphertext)))
		
				)).collect(Collectors.toList()));
	}

	public static EncBallot encBallot(Ballot b, BigInteger publicKey)
	{
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		Element<BigInteger> publicKeyElem = group.getElement(publicKey);
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		
		return new EncBallot(b.prefrences.stream().map(i -> new EncPrefrence(i.prefered, i.over, 
				new ElGamalCiphertext(elGamal.encrypt(publicKeyElem, generator.power(i.plaintext)))
				)).collect(Collectors.toList()));
		
		
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

