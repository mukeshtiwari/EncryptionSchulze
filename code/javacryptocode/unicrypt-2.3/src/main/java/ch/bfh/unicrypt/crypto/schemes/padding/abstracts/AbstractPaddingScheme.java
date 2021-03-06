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
package ch.bfh.unicrypt.crypto.schemes.padding.abstracts;

import ch.bfh.unicrypt.crypto.schemes.padding.interfaces.PaddingScheme;
import ch.bfh.unicrypt.crypto.schemes.scheme.abstracts.AbstractScheme;
import ch.bfh.unicrypt.helper.random.RandomByteSequence;
import ch.bfh.unicrypt.helper.random.hybrid.HybridRandomByteSequence;
import ch.bfh.unicrypt.math.algebra.concatenative.interfaces.ConcatenativeElement;
import ch.bfh.unicrypt.math.algebra.concatenative.interfaces.ConcatenativeSemiGroup;
import ch.bfh.unicrypt.math.algebra.general.interfaces.Element;
import ch.bfh.unicrypt.math.function.interfaces.Function;

/**
 *
 * @author R. Haenni
 * @param <MS> Message space
 * @param <ME> Message element
 * @param <PS> Padding space
 * @param <PE> Padding element
 */
public abstract class AbstractPaddingScheme<MS extends ConcatenativeSemiGroup, ME extends ConcatenativeElement, PS extends ConcatenativeSemiGroup, PE extends ConcatenativeElement>
	   extends AbstractScheme<MS>
	   implements PaddingScheme {

	private static final long serialVersionUID = 1L;

	protected final PS paddingSpace;
	private Function paddingFunction;

	protected AbstractPaddingScheme(MS messageSpace, PS paddingSpace) {
		super(messageSpace);
		this.paddingSpace = paddingSpace;
	}

	@Override
	public PS getPaddingSpace() {
		return this.paddingSpace;
	}

	@Override
	public Function getPaddingFunction() {
		if (this.paddingFunction == null) {
			this.paddingFunction = this.abstractGetPaddingFunction();
		}
		return this.paddingFunction;
	}

	@Override
	public PE pad(final Element element) {
		return this.pad(element, HybridRandomByteSequence.getInstance());
	}

	@Override
	public PE pad(final Element element, RandomByteSequence randomByteSequence) {
		return (PE) this.getPaddingFunction().apply(element, randomByteSequence);
	}

	@Override
	protected String defaultToStringContent() {
		return "" + this.messageSpace.getBlockLength();
	}

	protected abstract Function abstractGetPaddingFunction();

}
