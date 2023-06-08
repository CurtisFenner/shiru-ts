import { Components } from "./components.js";
import { DefaultMap, TrieMap } from "./data.js";

export type EObject = symbol & { __brand: "EObject" };

export type EClassDescription<Term> = {
	members: { id: EObject, term: Term, operands: EObject[] }[],
	representative: EObject,
};

type PendingCongruence = {
	left: EObject,
	right: EObject,
	leftOperands: EObject[],
	rightOperands: EObject[],
};

class TagTracker<Key, TagValues extends Record<string, unknown>> {
	private tags = new Map<
		keyof TagValues,
		Map<Key, TagValues[keyof TagValues]>
	>();

	private originals = new Map<
		keyof TagValues,
		{ original: Key, value: TagValues[keyof TagValues] }[]
	>();

	constructor(private merge: {
		[K in keyof TagValues]: (child: TagValues[K], parent: TagValues[K]) => TagValues[K]
	}) {
		this.clear();
	}

	clear(): void {
		this.tags.clear();
		for (const key in this.merge) {
			this.tags.set(key, new Map());
		}
		for (const [tag, values] of this.originals) {
			const map = this.tags.get(tag)!;
			for (const value of values) {
				const existing = map.get(value.original);
				if (existing === undefined) {
					map.set(value.original, value.value);
				} else {
					const merged = this.merge[tag](existing, value.value);
					map.set(value.original, merged);
				}
			}
		}
	}

	attach<Tag extends keyof TagValues>(
		tag: Tag,
		to: Key,
		value: TagValues[Tag],
		retainAfterClear: boolean,
		andParent: Key,
	): void {
		let byTag = this.tags.get(tag)!;
		this.mergeValueInto(tag, to, value, byTag);

		if (retainAfterClear) {
			// Re-add this attachment after clearing.
			const record = { original: to, value };
			let originalsByTag = this.originals.get(tag);
			if (originalsByTag === undefined) {
				originalsByTag = [];
				this.originals.set(tag, originalsByTag);
			}
			originalsByTag.push(record);
		}

		if (andParent !== to) {
			// Attach the tag to the parent, but do not remember this attachment
			// after clearing.
			this.mergeValueInto(tag, andParent, value, byTag);
		}
	}

	private mergeValueInto<Tag extends keyof TagValues>(
		tag: Tag,
		to: Key,
		value: TagValues[Tag],
		byTag = this.tags.get(tag)!,
	): void {
		const existing = byTag.get(to);
		if (existing === undefined) {
			byTag.set(to, value);
		} else {
			const merged = this.merge[tag](existing as TagValues[Tag], value);
			byTag.set(to, merged);
		}
	}

	getTagged<Tag extends keyof TagValues>(
		tag: Tag,
		on: Key,
	): TagValues[Tag] | null {
		const byTag = this.tags.get(tag);
		if (byTag === undefined) {
			return null;
		}
		const byKey = byTag.get(on);
		if (byKey === undefined) {
			return null;
		}
		return byKey as TagValues[Tag];
	}

	mergeInto(child: Key, parent: Key): void {
		for (const [tag, byTag] of this.tags) {
			const fromChild = byTag.get(child);
			if (fromChild === undefined) {
				continue;
			}
			this.mergeValueInto(tag, parent, fromChild, byTag);
		}
	}
}

/// An "equivalence-graph", loosely inspired by "egg (e-graphs good)".
export class EGraph<Term, TagValues extends Record<string, unknown>, Reason> {
	private tagTracker: TagTracker<EObject, TagValues>;

	/**
	 * The `tuples` triemap is used to "hashcons" objects with identical
	 * definitions.
	 */
	private tuples: TrieMap<[Term, ...EObject[]], EObject> = new TrieMap();

	private objectDefinition: Map<
		EObject,
		{ term: Term, operands: EObject[], uniqueObjectCount: number, extra: unknown }
	> = new Map();
	private components = new Components<EObject, Reason>();

	private lazyCongruence: PendingCongruence[] = [];

	/**
	 * Applications with at least one operand are recorded in this map.
	 * 
	 * Keys are the representatives of each operand. Only one application is
	 * recorded for each canonicalized operands tuple.
	 */
	private applicationCanonicalization: TrieMap<[Term, ...EObject[]], EObject> = new TrieMap();

	/**
	 * `applicationsByOperand.get(object)` includes the set of applications
	 * which have an operand congruent to `object`.
	 */
	private applicationsByOperand: DefaultMap<EObject, Set<EObject>> = new DefaultMap(() => new Set());

	/**
	 * Applications of function terms in this set *may* (but not necessarily
	 * will) have their congruence maintenance skipped as part of
	 * `this.updateCongruence()`.
	 * 
	 * This can be used for performance for applications which won't benefit
	 * from congruence (for example, due to a small input size or well-defined
	 * semantics)
	 */
	public excludeCongruenceIndexing: Set<Term> = new Set();

	constructor(
		private preMergeCallback: (
			a: EObject,
			b: EObject,
			simpleReason: Reason | null,
			lefts: EObject[],
			rights: EObject[],
		) => null | "cancel",
		tagTrackingMerges: { [K in keyof TagValues]: (child: TagValues[K], parent: TagValues[K]) => TagValues[K]; },
	) {
		this.tagTracker = new TagTracker(tagTrackingMerges);
	}

	/**
	 * Restores the invariants for applicationCanonicalization with respect to
	 * the given application.
	 * 
	 * This method must be called on each application with an operand whose
	 * representative has changed.
	 */
	private canonicalizeApplication(application: EObject): EObject {
		const definition = this.getDefinition(application);
		const operandRepresentatives = definition.operands.map(operand => this.getRepresentative(operand));
		const key: [Term, ...EObject[]] = [definition.term, ...operandRepresentatives];
		const canonical = this.applicationCanonicalization.get(key);
		if (canonical === undefined) {
			this.applicationCanonicalization.put(key, application);
			return application;
		} else if (canonical !== application) {
			if (!this.areCongruent(canonical, application)) {
				const canonicalDefinition = this.getDefinition(canonical);
				this.lazyCongruence.push({
					left: canonical,
					right: application,
					leftOperands: canonicalDefinition.operands,
					rightOperands: definition.operands,
				});
			}
		}

		return canonical;
	}

	private indexApplication(application: EObject) {
		const canonical = this.canonicalizeApplication(application);
		const definition = this.getDefinition(canonical);
		for (const operand of definition.operands) {
			const representative = this.getRepresentative(operand);
			this.applicationsByOperand.get(representative).add(canonical);
		}
	}

	private unindexApplication(application: EObject) {
		const canonical = this.canonicalizeApplication(application);
		const definition = this.getDefinition(canonical);
		for (const operand of definition.operands) {
			const representative = this.getRepresentative(operand);
			this.applicationsByOperand.get(representative).delete(canonical);
		}
	}

	reset(): void {
		this.components.reset();
		this.queryCache.clear();
		this.tagTracker.clear();
		this.lazyCongruence = [];

		this.applicationCanonicalization.clear();
		for (const [key, value] of this.tuples) {
			this.applicationCanonicalization.put(key, value);
		}

		this.resetApplicationsByOperand(new Set(this.objectDefinition.keys()));
	}

	private resetApplicationsByOperand(objects: Set<EObject>): void {
		this.applicationsByOperand.clear();
		for (const object of objects) {
			const definition = this.objectDefinition.get(object)!;
			if (!this.excludeCongruenceIndexing.has(definition.term)) {
				this.indexApplication(object);
			}
			for (const operand of definition.operands) {
				objects.add(operand);
			}
		}
	}

	/**
	 * `getDefinition(id)` returns the `term` and `operands` passed to
	 * `add(term, operands)` to create the given object.
	 */
	getDefinition(id: EObject): { term: Term, operands: EObject[], extra: unknown } {
		const definition = this.objectDefinition.get(id);
		if (definition === undefined) {
			throw new Error("EGraph.getDefinition: object `" + String(id) + "` not defined");
		}

		return {
			term: definition.term,
			operands: definition.operands,
			extra: definition.extra,
		};
	}

	getTagged<Tag extends keyof TagValues>(
		tag: Tag,
		id: EObject,
	): TagValues[Tag] | null {
		const representative = this.components.representative(id);
		const tagValue = this.tagTracker.getTagged(tag, representative);
		return tagValue;
	}

	debugSymbolNames = true;
	private uniqueObjectCount = 1;

	/**
	 * `hasStructure(term, operands)` searches for an object with the given
	 * definition, returning it if it was already created using
	 * `add(term, operands)`. The search is based on object identity, and not by
	 * equalities tracked by this `EGraph`.
	 * 
	 * `hasStructure` returns `null` when `add(term, operands)` has not already
	 * been invoked with the given term and operand objects.
	 */
	hasStructure(term: Term, operands: EObject[]): EObject | null {
		const tuple: [Term, ...EObject[]] = [term, ...operands];
		return this.tuples.get(tuple) || null;
	}

	addTag<Tag extends keyof TagValues>(object: EObject, tag: Tag, value: TagValues[Tag]): void {
		const representative = this.getRepresentative(object);
		this.tagTracker.attach(tag, object, value, true, representative);
	}

	add(term: Term, operands: EObject[], hint?: string, extra?: unknown): EObject {
		const tuple: [Term, ...EObject[]] = [term, ...operands];
		const existing = this.tuples.get(tuple);
		if (existing) {
			return existing;
		}

		if (!hint && this.debugSymbolNames) {
			const fnName = String(term).match(/^Symbol\((.+)\)$/);
			hint = (fnName ? fnName[1] : "unknown");
			if (operands.length !== 0) {
				const operandStrings = operands.map(x => {
					if (x === undefined) {
						throw new Error("EGraph.add: unexpected undefined");
					}
					const raw = String(x);
					const match = String(x).match(/^Symbol\(egraph-term    (.+)    \)$/);
					if (match) {
						return match[1];
					} else {
						return raw;
					}
				});
				if (operands.length === 2 && !hint.match(/^[a-zA-Z0-9]*$/)) {
					hint = `(${operandStrings[0]}) ${hint} (${operandStrings[1]})`;
				} else {
					hint = `${hint}(${operandStrings.join(", ")})`;
				}
			}
		}

		const id: EObject = Symbol("egraph-term    " + hint + " #" + this.uniqueObjectCount + "    ") as EObject;
		this.uniqueObjectCount += 1;
		this.tuples.put(tuple, id);
		this.objectDefinition.set(id, {
			term,
			operands,
			uniqueObjectCount: this.uniqueObjectCount,
			extra,
		});
		if (!this.excludeCongruenceIndexing.has(term)) {
			this.indexApplication(id);
		}
		this.canonicalizeApplication(id);
		return id;
	}

	/**
	 * The "reason" that this congruence is being added is the conjunction of
	 * `simpleReason` and the equalities `lefts[0] == rights[0] & ...`.
	 * 
	 * @returns false when this fact was already present in this egraph.
	 */
	mergeApplications(
		a: EObject,
		b: EObject,
		simpleReason: Reason | null,
		lefts: EObject[],
		rights: EObject[],
	): boolean {
		if (lefts.length !== rights.length) {
			throw new Error("EGraph.mergeBecauseCongruence: lefts.length !== rights.length");
		}

		const arep = this.components.representative(a);
		const brep = this.components.representative(b);
		if (arep === brep) {
			return false;
		}

		for (let i = 0; i < lefts.length; i++) {
			if (!this.areCongruent(lefts[i], rights[i])) {
				throw new Error("EGraph.mergeApplications: bad lefts/rights");
			}
		}

		if (this.preMergeCallback(a, b, simpleReason, lefts, rights) === "cancel") {
			return false;
		}

		const { child, parent } = this.components.predictRepresentativeOfMerge(a, b);

		const applicationsOfChild = [...this.applicationsByOperand.get(child)];
		for (const applicationOfChild of applicationsOfChild) {
			this.unindexApplication(applicationOfChild);
		}

		const dependencies = [];
		for (let i = 0; i < lefts.length; i++) {
			dependencies.push({ left: lefts[i], right: rights[i] });
		}
		this.components.addCongruence(a, b, simpleReason, dependencies);
		this.tagTracker.mergeInto(child, parent);

		// Restore application indexes
		for (const applicationOfChild of applicationsOfChild) {
			this.canonicalizeApplication(applicationOfChild);
			this.indexApplication(applicationOfChild);
		}

		return true;
	}

	updateCongruence(): boolean {
		let madeChanges = false;
		while (this.lazyCongruence.length !== 0) {
			const q = this.lazyCongruence;
			this.lazyCongruence = [];
			for (const e of q) {
				madeChanges = this.mergeApplications(e.left, e.right, null, e.leftOperands, e.rightOperands)
					|| madeChanges;
			}
		}
		return madeChanges;
	}

	private queryCache: Map<EObject, Map<EObject, Set<Reason>>> = new Map();

	areCongruent(a: EObject, b: EObject): boolean {
		return this.components.areCongruent(a, b);
	}

	explainCongruence(a: EObject, b: EObject): Set<Reason> {
		if (!this.components.areCongruent(a, b)) {
			throw new Error("EGraph.explainCongruence: objects are not congruent");
		}

		let cacheA = this.queryCache.get(a);
		if (cacheA !== undefined) {
			const cacheB = cacheA.get(b);
			if (cacheB !== undefined) {
				return cacheB;
			}
		}

		const seq = this.components.findPath(a, b);
		if (seq === null) {
			throw new Error(`EGraph.explainCongruence: expected path between ${String(a)} and ${String(b)}`);
		}
		if (cacheA === undefined) {
			cacheA = new Map();
			this.queryCache.set(a, cacheA);
		}
		cacheA.set(b, seq);
		return seq;
	}

	/// getRepresentative(obj) returns a "representative" element of obj's
	/// equivalence class, such that any two objects that are equal have the
	/// same representative, and any objects that are not equal have different
	/// representatives.
	getRepresentative(obj: EObject): EObject {
		return this.components.representative(obj);
	}

	getAllApplications(fn: Term): { id: EObject, operands: EObject[] }[] {
		const applications = this.tuples.getSuffixes(fn);
		const out: { id: EObject, operands: EObject[] }[] = [];
		if (applications === undefined) {
			return out;
		}
		for (const [operands, id] of applications) {
			out.push({ id, operands: operands.slice(0) });
		}
		return out;
	}
}
