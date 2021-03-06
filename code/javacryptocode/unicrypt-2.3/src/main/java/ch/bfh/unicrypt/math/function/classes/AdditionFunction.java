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
package ch.bfh.unicrypt.math.function.classes;

import ch.bfh.unicrypt.ErrorCode;
import ch.bfh.unicrypt.UniCryptRuntimeException;
import ch.bfh.unicrypt.helper.random.RandomByteSequence;
import ch.bfh.unicrypt.math.algebra.additive.interfaces.AdditiveElement;
import ch.bfh.unicrypt.math.algebra.additive.interfaces.AdditiveSemiGroup;
import ch.bfh.unicrypt.math.algebra.general.classes.ProductSemiGroup;
import ch.bfh.unicrypt.math.algebra.general.classes.Tuple;
import ch.bfh.unicrypt.math.algebra.general.interfaces.Element;
import ch.bfh.unicrypt.math.algebra.general.interfaces.Group;
import ch.bfh.unicrypt.math.function.abstracts.AbstractFunction;

/**
 * This interface represents the the concept of a function f:X^n->X, which applies the group operation sequentially to
 * several input elements. For this to work, the input elements is given as a tuple element of a corresponding power
 * group of arity n. For n=0, the function returns the group's identity element. For n=1, the function returns the
 * single element included in the tuple element.
 * <p/>
 * @see Group#apply(Element[])
 * @see Element#apply(Element)
 * <p/>
 * @author R. Haenni
 * @author R. E. Koenig
 * @version 2.0
 */
public class AdditionFunction
	   extends AbstractFunction<AdditionFunction, ProductSemiGroup, Tuple, AdditiveSemiGroup, AdditiveElement> {

	private static final long serialVersionUID = 1L;

	private AdditionFunction(final ProductSemiGroup domain, final AdditiveSemiGroup coDomain) {
		super(domain, coDomain);
	}

	@Override
	protected AdditiveElement abstractApply(final Tuple tuple, final RandomByteSequence randomByteSequence) {
		return this.getCoDomain().add(tuple);
	}

	public static AdditionFunction getInstance(final AdditiveSemiGroup additiveSemiGroup) {
		return AdditionFunction.getInstance(additiveSemiGroup, 2);
	}

	/**
	 * This is the general factory method of this class. The first parameter is the group on which it operates, and the
	 * second parameter is the number of input elements.
	 * <p/>
	 * @param additiveSemiGroup The group on which this function operates
	 * @param arity             The number of input elements
	 * @return The resulting function
	 */
	public static AdditionFunction getInstance(final AdditiveSemiGroup additiveSemiGroup, final int arity) {
		if (additiveSemiGroup == null) {
			throw new UniCryptRuntimeException(ErrorCode.NULL_POINTER);
		}
		if (arity < 0) {
			throw new UniCryptRuntimeException(ErrorCode.NEGATIVE_VALUE, arity);
		}
		return new AdditionFunction(ProductSemiGroup.getInstance(additiveSemiGroup, arity), additiveSemiGroup);
	}

}
