package schulze;


import java.math.BigInteger;
import java.text.DateFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;


import ch.bfh.unicrypt.UniCryptException;
import ch.bfh.unicrypt.crypto.mixer.classes.IdentityMixer;
import ch.bfh.unicrypt.crypto.mixer.classes.ReEncryptionMixer;
import ch.bfh.unicrypt.crypto.proofsystem.challengegenerator.classes.FiatShamirSigmaChallengeGenerator;
import ch.bfh.unicrypt.crypto.proofsystem.challengegenerator.interfaces.ChallengeGenerator;
import ch.bfh.unicrypt.crypto.proofsystem.challengegenerator.interfaces.SigmaChallengeGenerator;
import ch.bfh.unicrypt.crypto.proofsystem.classes.ElGamalEncryptionValidityProofSystem;
import ch.bfh.unicrypt.crypto.proofsystem.classes.EqualityPreimageProofSystem;
import ch.bfh.unicrypt.crypto.proofsystem.classes.PermutationCommitmentProofSystem;
import ch.bfh.unicrypt.crypto.proofsystem.classes.PlainPreimageProofSystem;
import ch.bfh.unicrypt.crypto.proofsystem.classes.ReEncryptionShuffleProofSystem;
import ch.bfh.unicrypt.crypto.schemes.commitment.classes.PermutationCommitmentScheme;
import ch.bfh.unicrypt.crypto.schemes.encryption.classes.ElGamalEncryptionScheme;
import ch.bfh.unicrypt.crypto.schemes.encryption.interfaces.ReEncryptionScheme;
import ch.bfh.unicrypt.helper.math.Permutation;
import ch.bfh.unicrypt.helper.prime.SafePrime;
import ch.bfh.unicrypt.helper.random.RandomOracle;
import ch.bfh.unicrypt.helper.random.deterministic.DeterministicRandomByteSequence;
import ch.bfh.unicrypt.math.algebra.dualistic.classes.ZMod;
import ch.bfh.unicrypt.math.algebra.dualistic.classes.ZModElement;
import ch.bfh.unicrypt.math.algebra.general.classes.Pair;
import ch.bfh.unicrypt.math.algebra.general.classes.PermutationElement;
import ch.bfh.unicrypt.math.algebra.general.classes.PermutationGroup;
import ch.bfh.unicrypt.math.algebra.general.classes.ProductGroup;
import ch.bfh.unicrypt.math.algebra.general.classes.Subset;
import ch.bfh.unicrypt.math.algebra.general.classes.Triple;
import ch.bfh.unicrypt.math.algebra.general.classes.Tuple;
import ch.bfh.unicrypt.math.algebra.general.interfaces.CyclicGroup;
import ch.bfh.unicrypt.math.algebra.general.interfaces.Element;
import ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModElement;
import ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModPrime;
import ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModSafePrime;
import ch.bfh.unicrypt.math.function.classes.GeneratorFunction;
import ch.bfh.unicrypt.math.function.classes.PermutationFunction;
import ch.bfh.unicrypt.math.function.classes.PowerFunction;
import ch.bfh.unicrypt.math.function.interfaces.Function;
import ch.bfh.unicrypt.crypto.encoder.classes.ZModPrimeToGStarModSafePrime;
import ch.bfh.unicrypt.crypto.keygenerator.interfaces.KeyPairGenerator;
import java.util.Arrays;

public class HelloWorld {
	
	//Simplification of java for OCaml
	
	//Begin data structures
	
	public static class ElGamalCiphertext {	//An ElGamal Ciphertext is represented as two BigIntegers
		public ElGamalCiphertext(BigInteger c1, BigInteger c2){
			this.c1 = c1;
			this.c2 = c2;
		}
		
		public ElGamalCiphertext(Pair c){
			this.c1 = c.getFirst().convertToBigInteger();
			this.c2 = c.getSecond().convertToBigInteger();
		}
		
		public String toString() {
			return c1.toString()+" "+c2.toString();
		}
		
		public BigInteger c1;
		public BigInteger c2;
	}
	
	public static class EncPreferenceWithZKP {	//An encrypted preference denotes that a candidate
		// is preferred over another, denoted preferred and over respectively, the ciphertext contains
		//encryption of the weight of this preference
		public EncPreferenceWithZKP( ElGamalCiphertext ciphertext, String ZKP) {
			this.ciphertext = ciphertext;
			this.ZKP = ZKP;
		}
		
		public String toString() {
			return ciphertext.toString()+" "+ZKP;
		}
		
		 public ElGamalCiphertext ciphertext;
		 public String ZKP;
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
		
		public String toString() {
			return plaintext.toString()+" "+ZKP;
		}
	}

	public static class EncBallot { //An encrypted ballot contains a list of encrypted preferences
		// it is expected that this list will be of length n^2 containing the preference relationship between
		// each candidate the all n candidates
		// TODO check that the EncPrefrence is correctly formed
		public EncBallot(List<ElGamalCiphertext> prefrences) {
			this.prefrences = prefrences;
		}
		
		public List<ElGamalCiphertext> prefrences;
		
		public String toString() {
			return prefrences.toString();
		}
	}
	
	public static class EncBallotWithZKP extends EncBallot { //An encrypted ballot contains a list of encrypted preferences
		// it is expected that this list will be of length n^2 containing the preference relationship between
		// each candidate the all n candidates
		// TODO check that the EncPrefrence is correctly formed
		public EncBallotWithZKP(List<EncPreferenceWithZKP> prefrences) {
			super(prefrences.stream().map(i -> i.ciphertext).collect(Collectors.toList()));
			this.ZKPs = prefrences.stream().map(i -> i.ZKP).collect(Collectors.toList());
		}
		
		private List<String> ZKPs;
		
		public List<EncPreferenceWithZKP> getEncPreferenceWithZKP(){
			return IntStream.range(0, ZKPs.size()).mapToObj(i -> new 
					EncPreferenceWithZKP(this.prefrences.get(i), ZKPs.get(i))).collect(Collectors.toList());
		}
		
		public String toString() {
			return prefrences.toString();
		}
	}
	
	public static class Ballot { //A ballot contains a list of preferences
		// it is expected that this list will be of length n^2 containing the preference relationship between
		// each candidate the all n candidates
		// TODO check that the preferences is correctly formed
		public Ballot(List<BigInteger> prefrences) {
			this.prefrences = prefrences;
		}
		
		public String toString() {
			return prefrences.toString();
		}
		
		public List<BigInteger> prefrences;
	}
	 
	public static class BallotWithZKP {//A ballot contains a list of preferences
		// it is expected that this list will be of length n^2 containing the preference relationship between
		// each candidate the all n candidates each preference contains a proof that is correctly decryted
		// TODO check that the preferences is correctly formed
		public BallotWithZKP(List<PrefrenceWithZKP> prefrences) {
			this.prefrences = prefrences;
		}
		
		public String toString() {
			return prefrences.toString();
		}
		
		public List<PrefrenceWithZKP> prefrences;
	}
	
	public static class EncBallotWithZKPOfPermutation extends EncBallot { //A ballot contains a list of preferences
		// it is expected that this list will be of length n^2 containing the preference relationship between
		// each candidate the all n candidates
		// this variant includes a string which contains a proof that this Ballot is the correct permutation of another
		// TODO check that the preferences is correctly formed
		public EncBallotWithZKPOfPermutation(List<ElGamalCiphertext> prefrences, String ZKP) {
			super(prefrences);
			this.ZKP = ZKP;
		}
		
		public String ZKP;
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
		return privateKey.getValue();
	}
	
	@SuppressWarnings("unchecked")
	public static BigInteger generatePK(BigInteger privateKey) throws UniCryptException { //Generates a public key from a secret key
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		KeyPairGenerator kpg = elGamal.getKeyPairGenerator();
		Element<BigInteger> publicKey = kpg.generatePublicKey(group.getZModOrder().getElement(privateKey));
		return publicKey.convertToBigInteger();
	}
	
	public static EncBallot EncBallotMulti(EncBallot b1, EncBallot b2) { //Takes two encrypted ballots
		//and produces a new encrypted ballot by pairwise multiplication of ciphertexts
		//TODO There are no checks to make sure such multiplication is possible
		return new EncBallot(
			IntStream.range(0, b1.prefrences.size()).mapToObj( //For all preferences
			i -> multiplyCiphertext(b1.prefrences.get(i),b2.prefrences.get(i)) //Multiply the ciphertexts
			).collect(Collectors.toList())
		);
	}
	
	//This function calculates the discrete log of element to the base generator 
	//TODO the function will run in infinite time if no log exists, there should be some limit imposed
	//TODO the function will run in nearly infinite time if the log is sufficently larger, some limit should be imposed
	public static BigInteger dLog(GStarModElement generator, Element<BigInteger> element) {
		BigInteger dlog = BigInteger.valueOf(IntStream.iterate(0, i -> i+1).filter(i -> generator.power(i).getValue().equals(element.getValue())).findFirst().getAsInt());
		//System.out.println("Dlog: "+dlog);
		return dlog;
	}
	
	//This function takes two BigIntegers representing group elements and produces their product in the group
	public static BigInteger groupOp(BigInteger element1, BigInteger element2) throws UniCryptException {
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement one = group.getElementFrom(element1);
		GStarModElement two = group.getElementFrom(element2);
		return one.multiply(two).getValue();
	}
	
	//This function takes two ElGamal ciphertexts and produces their product
	public static ElGamalCiphertext multiplyCiphertext(ElGamalCiphertext c1, ElGamalCiphertext c2) {
		try {
			ElGamalCiphertext c3 = new ElGamalCiphertext(groupOp(c1.c1, c2.c1), groupOp(c1.c2, c2.c2));
			//System.out.println(c1);
			//System.out.println(c2);
			//System.out.println(c3);
			return c3;
		} catch(Exception exp) {
			System.out.println("ERROR while multiplying ciphertexts");
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
		EqualityPreimageProofSystem equalityPreimageProofSystem = EqualityPreimageProofSystem.getInstance(f1, f1);
		//System.out.println(equalityPreimageProofSystem.getPrivateInputSpace());
		//System.out.println(equalityPreimageProofSystem.getPublicInputSpace());
		
		//Return
		return new BallotWithZKP(b.prefrences.stream().map(i -> {
			Tuple c = ciphertextConvBItT(elGamal, i);
			Element encodedMessage =  elGamal.decrypt(privateKeyElem, c);
			//System.out.println("Decryted Element: "+elGamal.decrypt(privateKeyElem, c).convertToBigInteger());
			GStarModElement partialDecryption = (GStarModElement) c.getLast();
			Pair publicInput = Pair.getInstance(group.power(generator, privateKeyElem), partialDecryption);
			Pair privateInput = Pair.getInstance(generator, privateKeyElem);
			//equalityPreimageProofSystem.generate(privateKeyElem, publicInput)   //Generate (private input and public input
			return new PrefrenceWithZKP(dLog(generator, encodedMessage),equalityPreimageProofSystem.generate(privateInput, publicInput).toString());
			}
		).collect(Collectors.toList()));
	}

	public static EncBallot encBallot(Ballot b, BigInteger publicKey)
	{
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		Element<BigInteger> publicKeyElem = group.getElement(publicKey);
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		
		return new EncBallot(b.prefrences.stream().map(i -> 
				new ElGamalCiphertext(elGamal.encrypt(publicKeyElem, generator.power(i)))
				).collect(Collectors.toList()));
		}
	
	//We should use this function to create ballots if the system was deployed
//	public static EncBallotWithZKP EncBallotZKP(Ballot b, BigInteger publicKey)
//	{
//		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
//		GStarModElement generator = group.getDefaultGenerator();
//		Element<BigInteger> publicKeyElem = group.getElement(publicKey);
//		ElGamalEncryptionScheme elGamal = 
//				ElGamalEncryptionScheme.getInstance(generator);
//		
//		Function f1  = PowerFunction.getInstance(group);
//		PlainPreimageProofSystem plainePreimageProofSystem = PlainPreimageProofSystem.getInstance(f1);
//		
//		return new EncBallotWithZKP(b.prefrences.stream().map(i -> {
//				Element random = elGamal.getRandomizationSpace().getRandomElement();
//				Pair c = elGamal.encrypt(publicKeyElem, generator.power(i),random);
//				return new EncPreferenceWithZKP(new ElGamalCiphertext(c),plainePreimageProofSystem.generate(random, c.getSecond()).convertToString());
//			}
//		).collect(Collectors.toList()));
//	}

	

	public static EncBallotWithZKP EncBallotZKPofPlaintextZero(int size, BigInteger publicKey) throws UniCryptException
	{
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		Element<BigInteger> publicKeyElem = group.getElement(publicKey);
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		
		Element<BigInteger> One = group.getElementFrom(BigInteger.ONE); //Encoding of the message zero
		
		return new EncBallotWithZKP(IntStream.range(0, size*size).mapToObj(i -> {
				Element random = elGamal.getRandomizationSpace().getElement(BigInteger.ONE);
				Pair c = elGamal.encrypt(publicKeyElem, One, random);
				return new EncPreferenceWithZKP(new ElGamalCiphertext(c),"The message is zero and the random coin is one");
			}
		).collect(Collectors.toList()));
	}

	//This function is same as EncBallotZKPofPlaintextZero, but here I am passing the ballot whose all entries are zero, public key and return 
	// Encrypted zero margin function with Zero knowledge proof. Implement it to make sure this matches with OCaml function. 
	// This function will be called for encrypting the zero margin function and publishing the zero knowledge proof for everyone else to verify it
	public static EncBallotWithZKP EncAndZKPofZeroMargin(Ballot b, BigInteger publicKey)
	{
        	GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
                GStarModElement generator = group.getDefaultGenerator();
                Element<BigInteger> publicKeyElem = group.getElement(publicKey);
                ElGamalEncryptionScheme elGamal = ElGamalEncryptionScheme.getInstance(generator);
		
		return new EncBallotWithZKP(b.prefrences.stream().map(i -> {
				Element random = elGamal.getRandomizationSpace().getElement(BigInteger.ONE);
				Pair c = elGamal.encrypt(publicKeyElem, generator.power(i) , random);
				return new EncPreferenceWithZKP(new ElGamalCiphertext(c),"The message is zero and the random coin is one");
			 } 
			).collect(Collectors.toList()));
			 
	}
		

	
	public static Triple createCiphertexts(Tuple uV, int size, CyclicGroup G_q, ReEncryptionScheme encryptionScheme, Element encryptionPK, PermutationElement pi) {

		final ZMod Z_q = G_q.getZModOrder();

		// Ciphertexts
		Tuple rV = ProductGroup.getInstance(Z_q, size).getRandomElement();
		Element[] uPrimes = new Element[size];
		for (int i = 0; i < size; i++) {
			uPrimes[i] = encryptionScheme.reEncrypt(encryptionPK, uV.getAt(i), rV.getAt(i));
		}
		Tuple uPrimeV = PermutationFunction.getInstance(ProductGroup.getInstance(G_q, 2), size).apply(Tuple.getInstance(uPrimes), pi);

		return Triple.getInstance(uV, uPrimeV, rV);
	}
	
	public static EncBallotWithZKPOfPermutation RowShuffleWithZKP(EncBallot b, BigInteger publicKey) {
		//Setup ElGamal
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		Element<BigInteger> publicKeyElem = group.getElement(publicKey);
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		
		//Setup Proof system
		int sqrt = (int) Math.sqrt(b.prefrences.size());
		ReEncryptionShuffleProofSystem proofSystem = ReEncryptionShuffleProofSystem.getInstance(sqrt, elGamal, publicKeyElem);
		final PermutationElement pi = PermutationGroup.getInstance(sqrt).getRandomElement();
		final DeterministicRandomByteSequence rrs = DeterministicRandomByteSequence.getInstance();
		PermutationCommitmentScheme pcs = PermutationCommitmentScheme.getInstance(group,sqrt, rrs);
		Tuple sV = pcs.getRandomizationSpace().getRandomElement();
		Tuple cPiV = pcs.commit(pi, sV); //This is the commitment to permutation
		//Prove permutation commitment
		PermutationCommitmentProofSystem pcps = 
				PermutationCommitmentProofSystem.getInstance(group, sqrt, rrs);
		String proof = pcps.generate(Pair.getInstance(pi, sV), cPiV).convertToString();
		
		List<ElGamalCiphertext> output = new ArrayList<ElGamalCiphertext>();
		
		//Mix and prove
		for (int i = 0; i < sqrt; i++) {
			Tuple ballots = Tuple.getInstance();
			
			for (int j = 0; j < sqrt; j++) {
				Element el = ciphertextConvBItT(elGamal,b.prefrences.get(i*sqrt+j));
				//System.out.println(el);
				ballots = ballots.add(el);
			}
						
			// Create ciphertexts (uV: input, uPrimeV: shuffled output, rV: randomness of re-encryption)
			final Triple c = createCiphertexts(ballots, sqrt, group, elGamal, publicKeyElem, pi);
			final Tuple uV = (Tuple) c.getFirst();  //Input
			final Tuple uPrimeV = (Tuple) c.getSecond(); //Shuffled
			final Tuple rV = (Tuple) c.getThird(); //Randomness
			Tuple privateInput = Tuple.getInstance(pi, sV, rV); 
			Tuple publicInput = Tuple.getInstance(cPiV, uV, uPrimeV);
			Tuple proofShuffle = proofSystem.generate(privateInput, publicInput);
			
			proof += proofShuffle.convertToString();
			for(int j = 0; j < sqrt; j++) {
				output.add(new ElGamalCiphertext((Pair) uPrimeV.getAt(j)));
			}
		}
		return new EncBallotWithZKPOfPermutation(output, proof);
	}
		

	public static EncBallotWithZKPOfPermutation ColumnShuffleWithZKP(EncBallot b, BigInteger publicKey) {
		//Setup ElGamal
		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
		GStarModElement generator = group.getDefaultGenerator();
		Element<BigInteger> publicKeyElem = group.getElement(publicKey);
		ElGamalEncryptionScheme elGamal = 
				ElGamalEncryptionScheme.getInstance(generator);
		
		//Setup Proof system
		int sqrt = (int) Math.sqrt(b.prefrences.size());
		ReEncryptionShuffleProofSystem proofSystem = ReEncryptionShuffleProofSystem.getInstance(sqrt, elGamal, publicKeyElem);
		final PermutationElement pi = PermutationGroup.getInstance(sqrt).getRandomElement();
		final DeterministicRandomByteSequence rrs = DeterministicRandomByteSequence.getInstance();
		PermutationCommitmentScheme pcs = PermutationCommitmentScheme.getInstance(group,sqrt, rrs);
		Tuple sV = pcs.getRandomizationSpace().getRandomElement();
		Tuple cPiV = pcs.commit(pi, sV); //This is the commitment to permutation
		//Prove permutation commitment
		PermutationCommitmentProofSystem pcps = 
				PermutationCommitmentProofSystem.getInstance(group, sqrt, rrs);
		String proof = pcps.generate(Pair.getInstance(pi, sV), cPiV).convertToString();
		
		ElGamalCiphertext[] output = new ElGamalCiphertext[sqrt*sqrt];
		
		//Mix and prove
		for (int i = 0; i < sqrt; i++) {
			Tuple ballots = Tuple.getInstance();
			
			for (int j = 0; j < sqrt; j++) {
				Element el = ciphertextConvBItT(elGamal,b.prefrences.get(i+sqrt*j));
				//System.out.println(el);
				ballots = ballots.add(el);
			}
						
			// Create ciphertexts (uV: input, uPrimeV: shuffled output, rV: randomness of re-encryption)
			final Triple c = createCiphertexts(ballots, sqrt, group, elGamal, publicKeyElem, pi);
			final Tuple uV = (Tuple) c.getFirst();  //Input
			final Tuple uPrimeV = (Tuple) c.getSecond(); //Shuffled
			final Tuple rV = (Tuple) c.getThird(); //Randomness
			Tuple privateInput = Tuple.getInstance(pi, sV, rV); 
			Tuple publicInput = Tuple.getInstance(cPiV, uV, uPrimeV);
			Tuple proofShuffle = proofSystem.generate(privateInput, publicInput);
			
			proof += proofShuffle.convertToString();
			for(int j = 0; j < sqrt; j++) {
				output[i+sqrt*j]= new ElGamalCiphertext((Pair) uPrimeV.getAt(j));
			}
		}
		return new EncBallotWithZKPOfPermutation(Arrays.asList(output), proof);
	}

		public static BigInteger add_for(BigInteger n, BigInteger m)
		{
			return n.add(m);
		}
		
		//////
		// Utility functions
		//////
		
		@SuppressWarnings("unchecked")
		public static Ballot generateRandomBallot(int size) {
			List<Integer> order = IntStream.range(0, size).mapToObj(i -> (Integer) i).collect(Collectors.toList());
			java.util.Collections.shuffle(order); //Order now contains an order on the candidates 0 to (N-1) in preference order
			//Technically a encrypted ballot in OCaml is (A, A, (0, 0)); (A, B, (1, 0)); (A, C, (1, 0)); (B, A, (0, 0)); (B, B, (0, 0)); (B, C, (0, 0)); (C, A, (0, 0)); (C, B, (1, 0)); (C, C, (0, 0))
			//but we only pass array of pairs (EncPreference) to Java code [(0, 0) (1, 0) (1, 0) (0, 0)  (0, 0) (0, 0) (0, 0) (1, 0) (0, 0)]
			return new Ballot(IntStream.range(0, size*size).mapToObj(i -> {
				//order.get(i/size) Prefered
				//over.get(i%size) Over
				if (order.indexOf(i/size) < order.indexOf(i%size)) {return BigInteger.ONE;}
				else {return BigInteger.ZERO;}
			}).collect(Collectors.toList()));
		}
	
		// This function takes Array of BigIntegers from OCaml code and returns 
		// plainttext. Assuming that we have two candidates, our Array b would of size 4 (n X n for candidate size n and will be interpreted as matrix )
		public static Ballot constructBallot(BigInteger[] b)
		{

			return new Ballot(Arrays.asList(b));
		}

		// This function is same as old one (n X n) matrix, but values are taken in pair (i, i + 1)
		// Try to change this funciton into lambda function
		public static EncBallot constructEncBallot (BigInteger[] b)
		{

			List<ElGamalCiphertext> encbal = new ArrayList<ElGamalCiphertext>();
			for(int i = 0; i < b.length; i+= 2)
			{ 
				encbal.add(new ElGamalCiphertext(b[i], b[i+1]));
			}
			return new EncBallot(encbal);
		}

		// This function converts ballots back to list of BigInteger
		public static BigInteger[] destructBallot(Ballot b)
		{
			return (BigInteger[]) b.prefrences.toArray();
		}


		// Converts Encrypted ballot into Array of BigInteger
		public static BigInteger[] destructEncBallot(EncBallot b)
		{
			List<ElGamalCiphertext> t = b.prefrences;
			int len = t.size();
			BigInteger[] bal = new BigInteger [2*len];
			for(int i = 0, j = 0; i < len; i++, j += 2)
			{
				bal[j] = t.get(i).c1;
				bal[j+1] = t.get(i).c2;
			}
			return bal;
		}

		// this is alos for testing purpose
		public static BigInteger[] addEncBallot(BigInteger[] n, BigInteger[] m)
		{
			
			BigInteger[] ret = new BigInteger[n.length];
			for(int i = 0 ; i < n.length; i++)
				ret[i] = n[i].add(m[i]);
			return ret;
		}
	
		public static BigInteger[] encBallotMultWrapper(BigInteger[] n, BigInteger[] m)
                {

                        int len = n.length;
			EncBallot f = constructEncBallot(n);
			EncBallot s = constructEncBallot(m);
			EncBallot t = EncBallotMulti(f, s);
                        return destructEncBallot(t);
                }
		// This function takes plain text ballot in terms of BigInteger Array
		// converts it to Ballot and encrypt it and returns the encrypted ballot again 
		// in terms of BigInteger Array
		public static BigInteger[] encBallotWrapper(BigInteger[] bal, BigInteger publickey)
		{
			return destructEncBallot(encBallot(constructBallot(bal), publickey));
		}

		// This function is simplification of decBallotZkp for the moment
		public static BigInteger[] decBallot(BigInteger[] bal, BigInteger privatekey)
		{
			BallotWithZKP b = decBallotZKP(constructEncBallot(bal), privatekey);
			List<PrefrenceWithZKP> lst = b.prefrences;
			int len = lst.size();
			BigInteger[] ret = new BigInteger[len];
			for(int i = 0; i < len; i++) 
				ret[i] = lst.get(i).plaintext;
			return ret;
		}

		// Zero Knowledge proof of decryption of ballot
		public static String decBallotZeroknowledge(BigInteger[] bal, BigInteger privatekey)
                {
                        BallotWithZKP b = decBallotZKP(constructEncBallot(bal), privatekey);
                        List<PrefrenceWithZKP> lst = b.prefrences;
			int len = lst.size();
			String ret = "";
			for (int i = 0; i < len; i++) ret = ret + " " + lst.get(i).ZKP;
			return ret; 
                }

	

		// This function is simplification of RowShuffleWithZKP, and returns the first 
		// data structure. Rowshuffled Encrypted ballot as Array of BigInteger
		public static BigInteger[] rowShuffle(BigInteger[] bal, BigInteger publickey)
		{
			EncBallotWithZKPOfPermutation b = RowShuffleWithZKP(constructEncBallot(bal), publickey);
			List<ElGamalCiphertext> lst = b.prefrences;
			int len = lst.size();
			BigInteger[] ret = new BigInteger[2*len];
			for(int i=0, j= 0; i < len; i++, j += 2)
			{
				ret[j] = lst.get(i).c1;
				ret[j+1] = lst.get(i).c2;
			}
			return ret;
		}

		// This function is simplification of  RowShuffleWithZKP, and returns the second 
		// data structure, String as ZeroKnowledge Proof of rowshuffle
		public static String rowShuffleZKP(BigInteger[] bal, BigInteger publickey)
                {
                        EncBallotWithZKPOfPermutation b = RowShuffleWithZKP(constructEncBallot(bal), publickey);
                        return b.ZKP;
                }
	
		// This function is simplification of columnShuffleZKP and return the first data structure 
		// column shuffled ballots
		public static BigInteger[] columnShuffle(BigInteger[] bal, BigInteger publickey)
		{
			EncBallotWithZKPOfPermutation b = ColumnShuffleWithZKP(constructEncBallot(bal), publickey);
			List<ElGamalCiphertext> lst = b.prefrences;
                        int len = lst.size();
                        BigInteger[] ret = new BigInteger[2*len];
                        for(int i=0, j= 0; i < len; i++, j += 2)
                        {
                                ret[j] = lst.get(i).c1;
                                ret[j+1] = lst.get(i).c2;
                        }
                        return ret;
		}
		
		public static String columnShuffleZKP(BigInteger[] bal, BigInteger publickey)
                {
                        EncBallotWithZKPOfPermutation b = ColumnShuffleWithZKP(constructEncBallot(bal), publickey);
			return b.ZKP;
                }


	public static void main(String[] args) throws UniCryptException {
		
		/////////////////
		//
		//A test case for three candidates and ten votes
		//
		/////////////////////
	
		System.out.println("Hello World");

		int NumCandidates = 3;
		int NumVoters = 10;
		
		//Generate random ballots
		List<Ballot> votes = IntStream.range(0, NumVoters).mapToObj(i -> generateRandomBallot(NumCandidates)).collect(Collectors.toList());
		System.out.println(votes.toString());
		
		//Encrypt the random ballots
		BigInteger sk = generateSK();
		System.out.println(sk);
		BigInteger pk = generatePK(sk);
		System.out.println(pk);
		BigInteger[] bal = new BigInteger[8];
		for(int i = 0; i < 8; i++) bal[i] = BigInteger.ZERO;
		BigInteger[] encmar = encBallotWrapper(bal, pk);
		for (int i = 0; i < encmar.length; i++) System.out.println(encmar[i].toString());
		
		
		/* 
		List<EncBallot> encVotes = votes.stream().map(i -> encBallot(i,pk)).collect(Collectors.toList());
		System.out.println(encVotes.toString());
		
		//Begin Multiplying
		EncBallot MarginFunction = EncBallotZKPofPlaintextZero(NumCandidates, pk);
		//System.out.println(MarginFunction);
		for(int i = 0; i < NumVoters; i++) {
			EncBallot rowBallot = RowShuffleWithZKP(encVotes.get(i), pk);
			EncBallot columnBallot = ColumnShuffleWithZKP(rowBallot, pk);
			BallotWithZKP maybeValidBallot = decBallotZKP(columnBallot,sk);
			System.out.println("Permuted ballot: ");
			maybeValidBallot.prefrences.forEach(j -> System.out.println(j.plaintext));
			
			MarginFunction = EncBallotMulti(MarginFunction, encVotes.get(i));
		}
		//System.out.println(MarginFunction);
		
		//Decrypt
		BallotWithZKP DecMarginFunction = decBallotZKP(MarginFunction,sk);
		System.out.println("DecMarginFunction: ");
		DecMarginFunction.prefrences.forEach(i -> System.out.println(i.plaintext));
		
		// Write Public key and Private Key in file. For testing purpose, make private key 1 and public key generator
		// We Start from OCaml main function and read a Encrypted ballot, Convert it in Java Array (EncBallot data structure) 
		// and call multiplyBallot. Takes the EncBallot and convert it to OCaml Array 
		//
		

//		ElGamalCiphertext c = new ElGamalCiphertext(BigInteger.ONE, BigInteger.ONE);
//		ElGamalCiphertext c = new ElGamalCiphertext(BigInteger.ONE, BigInteger.ONE);
//		
//		GStarModPrime group = GStarModSafePrime.getInstance(SafePrime.getSmallestInstance(128));
//		Element generator = group.getDefaultGenerator();
//		System.out.println(group.getModulus());
//		System.out.println(generator);
//		ElGamalEncryptionScheme elGamal = 
//				ElGamalEncryptionScheme.getInstance(generator);
//		KeyPairGenerator kpg = elGamal.getKeyPairGenerator();
//		Element<BigInteger> privateKey = kpg.generatePrivateKey();
//		Element<BigInteger> publicKey = kpg.generatePublicKey(privateKey);
//		System.out.println(privateKey);
//		System.out.println(publicKey);
//		
//		Element<BigInteger> cc = group.power(generator, 1); //g^m
//		System.out.println(cc);
//		Pair ciphertext = elGamal.encrypt(publicKey, cc);
//		System.out.println(ciphertext);
//		Element plaintext = elGamal.decrypt(privateKey, ciphertext);
//		System.out.println(plaintext);
		
		
		
		
		
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

