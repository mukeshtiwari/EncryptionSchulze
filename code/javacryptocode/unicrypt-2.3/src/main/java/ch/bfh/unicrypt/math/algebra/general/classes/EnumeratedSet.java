/*
 * UniCrypt
 *
 *  UniCrypt(tm): Cryptographical framework allowing the implementation of cryptographic protocols e.g. e-voting
 *  Copyright (c) 2016 Bern University of Applied Sciences (BFH), Research Institute for
 *  Security in the Information Society (RISIS), E-Voting Group (EVG)
 *  Quellgasse 21, CH-2501 Biel, Switzerland
 *
 *  Licensed under Dual License consisting of:
 *  1. GNU Affero General Public License (AGPL) v3
 *  and
 *  2. Commercial license
 *
 *
 *  1. This program is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Affero General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Affero General Public License for more details.
 *
 *   You should have received a copy of the GNU Affero General Public License
 *   along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 *  2. Licensees holding valid commercial licenses for UniCrypt may use this file in
 *   accordance with the commercial license agreement provided with the
 *   Software or, alternatively, in accordance with the terms contained in
 *   a written agreement between you and Bern University of Applied Sciences (BFH), Research Institute for
 *   Security in the Information Society (RISIS), E-Voting Group (EVG)
 *   Quellgasse 21, CH-2501 Biel, Switzerland.
 *
 *
 *   For further information contact <e-mail: unicrypt@bfh.ch>
 *
 *
 * Redistributions of files must retain the above copyright notice.
 */
package ch.bfh.unicrypt.math.algebra.general.classes;

import ch.bfh.unicrypt.ErrorCode;
import ch.bfh.unicrypt.UniCryptRuntimeException;
import ch.bfh.unicrypt.helper.converter.abstracts.AbstractBigIntegerConverter;
import ch.bfh.unicrypt.helper.converter.interfaces.Converter;
import ch.bfh.unicrypt.helper.random.RandomByteSequence;
import ch.bfh.unicrypt.helper.sequence.Sequence;
import ch.bfh.unicrypt.math.algebra.general.abstracts.AbstractSet;
import ch.bfh.unicrypt.math.algebra.general.interfaces.Set;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

/**
 *
 * @author R. Haenni <rolf.haenni@bfh.ch>
 * @param <V>
 */
public class EnumeratedSet<V>
	   extends AbstractSet<EnumeratedSetElement<V>, V> {

	private static final long serialVersionUID = 1L;

	protected final Map<Integer, V> valueMap;
	protected final Map<V, Integer> indexMap;

	public EnumeratedSet(Map<Integer, V> valueMap, Map<V, Integer> indexMap, Class<V> valueClass) {
		super(valueClass);
		this.valueMap = valueMap;
		this.indexMap = indexMap;
	}

	@Override
	protected BigInteger abstractGetOrder() {
		return BigInteger.valueOf(this.valueMap.size());
	}

	@Override
	protected boolean abstractContains(V value) {
		return this.indexMap.containsKey(value);
	}

	@Override
	protected EnumeratedSetElement<V> abstractGetElement(V value) {
		return new EnumeratedSetElement<>(this, value);
	}

	@Override
	protected Converter<V, BigInteger> abstractGetBigIntegerConverter() {
		return new AbstractBigIntegerConverter<V>(null) { // class parameter not needed

			@Override
			protected BigInteger abstractConvert(V value) {
				return BigInteger.valueOf(indexMap.get(value));
			}

			@Override
			protected V abstractReconvert(BigInteger value) {
				return valueMap.get(value.intValue());
			}
		};
	}

	@Override
	protected Sequence<EnumeratedSetElement<V>> abstractGetRandomElements(RandomByteSequence randomByteSequence) {
		return randomByteSequence.getRandomIntegerSequence(this.getOrder().intValue() - 1)
			   .map(index -> abstractGetElement(valueMap.get(index)));
	}

	@Override
	protected boolean abstractEquals(Set set) {
		EnumeratedSet<?> other = (EnumeratedSet<?>) set;
		return this.valueMap.equals(other.valueMap);
	}

	@Override
	protected int abstractHashCode() {
		return this.valueMap.hashCode();
	}

	@Override
	protected String defaultToStringContent() {
		String str = this.valueMap.values().toString();
		return str.substring(1, str.length() - 1);
	}

	public static <V> EnumeratedSet<V> getInstance(V... values) {
		if (values == null) {
			throw new UniCryptRuntimeException(ErrorCode.NULL_POINTER);
		}
		if (values.length == 0) {
			throw new UniCryptRuntimeException(ErrorCode.INVALID_LENGTH, values);
		}
		// both maps are needed for efficiency reasons
		Map<Integer, V> valueMap = new HashMap<>();
		Map<V, Integer> indexMap = new HashMap<>();
		int index = 0;
		for (V value : values) {
			if (value == null) {
				throw new UniCryptRuntimeException(ErrorCode.NULL_POINTER, values);
			}
			if (valueMap.containsValue(value)) {
				throw new UniCryptRuntimeException(ErrorCode.DUPLICATE_VALUE, values, value);
			}
			valueMap.put(index, value);
			indexMap.put(value, index);
			index++;
		}
		return new EnumeratedSet<>(valueMap, indexMap, (Class<V>) values.getClass().getComponentType());
	}

}
