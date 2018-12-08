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


/* This file is for unicrypt crypto primitives. We pass everything from OCaml to here as 
   string object and wrappers here change them to suitable Java datastruture */

public class CryptoWrapper {

	// EqualityPreimageProofSystem for constructing zero knowledge proof of honest decryption
        public static EqualityPreimageProofSystem getInstance(GeneratorFunction g, GeneratorFunction c1)
        {
		return EqualityPreimageProofSystem.getInstance(g, c1);
	}
	 
	// Write baby step giant step algorithm or Pollard Rho method to compute discrete logarithm
	 public static BigInteger dLog(GStarModElement generator, Element<BigInteger> element) {
			BigInteger dlog = BigInteger.valueOf(IntStream.iterate(0, i -> i+1).filter(i -> generator.power(i).getValue().equals(element.getValue())).findFirst().getAsInt());
			return dlog;
	}	

	// Main method to test the code 
	public static void main(String[] args) {
          System.out.println("Hello world");        
	}

}

