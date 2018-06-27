package schulze;


import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;


import ch.bfh.unicrypt.UniCryptException;
import ch.bfh.unicrypt.crypto.proofsystem.classes.EqualityPreimageProofSystem;
import ch.bfh.unicrypt.crypto.proofsystem.classes.PermutationCommitmentProofSystem;
import ch.bfh.unicrypt.crypto.proofsystem.classes.ReEncryptionShuffleProofSystem;
import ch.bfh.unicrypt.crypto.schemes.commitment.classes.PermutationCommitmentScheme;
import ch.bfh.unicrypt.crypto.schemes.encryption.classes.ElGamalEncryptionScheme;
import ch.bfh.unicrypt.crypto.schemes.encryption.interfaces.ReEncryptionScheme;
import ch.bfh.unicrypt.helper.prime.SafePrime;
import ch.bfh.unicrypt.helper.random.deterministic.DeterministicRandomByteSequence;
import ch.bfh.unicrypt.math.algebra.dualistic.classes.ZMod;
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
import ch.bfh.unicrypt.math.function.classes.PermutationFunction;
import ch.bfh.unicrypt.math.function.classes.PowerFunction;
import ch.bfh.unicrypt.math.function.interfaces.Function;
import ch.bfh.unicrypt.crypto.keygenerator.interfaces.KeyPairGenerator;
import ch.bfh.unicrypt.math.algebra.dualistic.classes.ZModElement;
import java.util.Arrays;



public class CryptoWrapper {

	/* This function takes safeprime and constructs safe prime */
        public static SafePrime safePrimeFromString(String str)
	{
		return SafePrime.getInstance(new BigInteger(str));
	}

	/* Construct Group Data Strucutre from Safe Prime passed from OCaml Code */
   	public static GStarModPrime groupFromSafePrime (SafePrime prime)
	{
		return  GStarModSafePrime.getInstance(prime);
	}

        /* Constructs Generator from string passed from OCaml. No Error checking so if you pass a generator which is not generator of group then 
           We will get unicrypt exception */
	public static GStarModElement generatorFromString (GStarModPrime group, String str)
	{
		return group.getElement(new BigInteger(str));
	} 

	/* This function returns ElGamal Encryption Scheme from group generator */
	public static ElGamalEncryptionScheme encryptionSchemeFromGroupGenerator(GStarModElement generator)
	{
		return ElGamalEncryptionScheme.getInstance(generator);
	}	

	/* This function generates publickey from group and string */
	public static GStarModElement generatePublicKeyFromString (GStarModPrime group, String str)
	{
		return group.getElement(new BigInteger(str));
	}
	
	/* This function generates privatekey from group and string */
	public static ZModElement generatePrivateKeyFromString (GStarModPrime group, String str)
	{
		return group.getZModOrder().getElement(new BigInteger(str));
	}
	
	// This function encrypts the message m as g^m
	public static String encryptMessage(String safeprime, String gen, String pubkey, String message)
	{
		GStarModPrime group = groupFromSafePrime(safePrimeFromString(safeprime));
		GStarModElement generator = generatorFromString (group, gen);
		ElGamalEncryptionScheme elGamal = encryptionSchemeFromGroupGenerator(generator);
		GStarModElement publickey = generatePublicKeyFromString(group, pubkey);
		Tuple c =  elGamal.encrypt(publickey, 
					generator.power(new BigInteger(message)));
		String fs = c.getFirst().convertToBigInteger().toString();
		String ss = c.getLast().convertToBigInteger().toString();
		return fs + "," + ss;				
	}

	public static String constructDecryptionZeroKnowledgeProof(String safeprime, String gen, String prikey, String pubkey, String ciphertext)
        {
		GStarModPrime group = groupFromSafePrime(safePrimeFromString(safeprime));
                GStarModElement generator = generatorFromString (group, gen);
                ElGamalEncryptionScheme elGamal = encryptionSchemeFromGroupGenerator(generator);
                GStarModElement publickey = generatePublicKeyFromString(group, pubkey);
		ZModElement privatekey = generatePrivateKeyFromString(group, prikey);
                // Split the ciphertext in the middle
                String[] ct = ciphertext.split(",");
       		try {
             		Tuple c = elGamal.getEncryptionSpace().getElementFrom(new BigInteger(ct[0]), 
            			 new BigInteger(ct[1]));
             		Element encodedMessage = elGamal.decrypt(privatekey, c); // Decrypt the message 
             		GStarModElement partialDecryption = (GStarModElement) c.getLast();	
             		partialDecryption = partialDecryption.applyInverse(encodedMessage);
             		Function g  = GeneratorFunction.getInstance(generator);
             		Function c1  = GeneratorFunction.getInstance(c.getFirst());
 			EqualityPreimageProofSystem equalityPreimageProofSystem = EqualityPreimageProofSystem.getInstance(g, c1); 
 			Pair publicInput = Pair.getInstance(group.power(generator, privatekey), partialDecryption);
 			//Construct Proof
 			Triple s = equalityPreimageProofSystem.generate(privatekey, publicInput);
 			// System.out.println(equalityPreimageProofSystem.verify(s, publicInput));
 			return s.toString();
             	}
             	catch(UniCryptException e)
             	{ 
            		 return "Something went Wrong"; 
             	}		
	}

	public static boolean verifyDecryptionZeroKnowledgeProof(String safeprime, String gen, String pubkey, String mess, String cipertext, String zkp)
	{
		return true;
	}

        // This function would return the g^m and pass it throw the descrete log to get m
	public static String decryptCiphertext(String safeprime, String gen, String prikey, String pubkey, String ciphertext)
     	{
             GStarModPrime group = groupFromSafePrime(safePrimeFromString(safeprime));
             GStarModElement generator = generatorFromString (group, gen);
             ElGamalEncryptionScheme elGamal = encryptionSchemeFromGroupGenerator(generator);
             GStarModElement publickey = generatePublicKeyFromString(group, pubkey);
             ZModElement privatekey = generatePrivateKeyFromString(group, prikey);
             String[] ct = ciphertext.split(",");
             try {
                     Tuple c = elGamal.getEncryptionSpace().getElementFrom(new BigInteger(ct[0]),
                              new BigInteger(ct[1]));
                     Element encodedMessage = elGamal.decrypt(privatekey, c); 
                     return encodedMessage.convertToBigInteger().toString();
                 }
             catch(UniCryptException e)
             { 
            	 return "Something went wrong in decryption"; 
             }

     	}	
	// Main method to test the code 
	public static void main(String[] args) {
		GStarModPrime groupstr = groupFromSafePrime(safePrimeFromString("170141183460469231731687303715884114527"));
		GStarModElement generatorstr = generatorFromString (groupstr, "4");
		ElGamalEncryptionScheme elGamalstr = encryptionSchemeFromGroupGenerator(generatorstr);
		GStarModElement publickeystr = generatePublicKeyFromString(groupstr, "49228593607874990954666071614777776087");
		ZModElement privatekeystr = generatePrivateKeyFromString(groupstr, "60245260967214266009141128892124363925");
	        String ciphertext = encryptMessage("170141183460469231731687303715884114527", 
				"4", "49228593607874990954666071614777776087", "1");
		String zeroknowledge = constructDecryptionZeroKnowledgeProof("170141183460469231731687303715884114527", 
				"4", "60245260967214266009141128892124363925", 
				"49228593607874990954666071614777776087", 
				"26361901114993279192003564171198272815,96243812141899119673335679145128031767");		
		
		String plaintext = decryptCiphertext ("170141183460469231731687303715884114527",
	    		"4", "60245260967214266009141128892124363925", "49228593607874990954666071614777776087", 
	    		ciphertext);
		System.out.println(groupstr.toString());
		System.out.println(generatorstr.toString());
		System.out.println(elGamalstr.toString()); 
		System.out.println(publickeystr.toString());
		System.out.println(privatekeystr.toString());
                System.out.println(ciphertext);
                System.out.println(zeroknowledge);
		System.out.println(plaintext);		
                

	}

}

