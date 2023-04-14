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

	private tuples: TrieMap<[Term, ...EObject[]], EObject> = new TrieMap();
	private objectDefinition: Map<EObject, { term: Term, operands: EObject[], uniqueObjectCount: number }> = new Map();
	private components = new Components<EObject, Reason>();

	private lazyCongruence: PendingCongruence[] = [];

	/**
	 * A canonicalized version of the function is added.
	 */
	private functionByRep: TrieMap<[Term, ...EObject[]], EObject> = new TrieMap();

	private references: DefaultMap<EObject, Set<EObject>> = new DefaultMap(() => new Set());

	constructor(
		private preMergeCallback: (a: EObject, b: EObject, simpleReason: Reason | null, lefts: EObject[], rights: EObject[]) => null | "cancel",
		tagTrackingMerges: { [K in keyof TagValues]: (child: TagValues[K], parent: TagValues[K]) => TagValues[K]; },
	) {
		this.tagTracker = new TagTracker(tagTrackingMerges);
	}

	private updateFunctionRep(obj: EObject): [Term, ...EObject[]] {
		const def = this.objectDefinition.get(obj)!!;
		const representativeKey: [Term, ...EObject[]] = [def.term];
		for (const operand of def.operands) {
			representativeKey.push(this.getRepresentative(operand));
		}

		const existing = this.functionByRep.get(representativeKey);
		if (existing !== undefined && existing !== obj) {
			const existingDef = this.getDefinition(existing);
			this.lazyCongruence.push({
				left: existing,
				right: obj,
				leftOperands: existingDef.operands,
				rightOperands: def.operands,
			});
		} else {
			this.functionByRep.put(representativeKey, obj);
		}
		return representativeKey;
	}

	reset(): void {
		this.components.reset();
		this.queryCache.clear();
		this.tagTracker.clear();
		this.references.clear();
		this.functionByRep.clear();
		this.lazyCongruence = [];
		for (const [object, { term, operands }] of this.objectDefinition) {
			this.functionByRep.put([term, ...operands], object);
			for (const operand of operands) {
				this.references.get(operand).add(object);
			}
		}
	}

	/**
	 * `getDefinition(id)` returns the `term` and `operands` passed to
	 * `add(term, operands)` to create the given object.
	 */
	getDefinition(id: EObject): { term: Term, operands: EObject[] } {
		const definition = this.objectDefinition.get(id);
		if (definition === undefined) {
			throw new Error("EGraph.getDefinition: object `" + String(id) + "` not defined");
		}
		return { term: definition.term, operands: definition.operands };
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

	add(term: Term, operands: EObject[], hint?: string): EObject {
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
		});
		this.functionByRep.put(tuple, id);
		for (const operand of operands) {
			this.references.get(this.getRepresentative(operand)).add(id);
		}
		this.updateFunctionRep(id);
		return id;
	}

	/**
	 * The "reason" that this congruence is being added is the conjunction of
	 * `simpleReason` and the equalities `lefts[0] == rights[0] & ...`.
	 * 
	 * @returns false when this fact was already present in this egraph.
	 */
	mergeApplications(a: EObject, b: EObject, simpleReason: Reason | null, lefts: EObject[], rights: EObject[]): boolean {
		if (lefts.length !== rights.length) {
			throw new Error("EGraph.mergeBecauseCongruence: lefts.length !== rights.length");
		}

		const arep = this.components.representative(a);
		const brep = this.components.representative(b);
		if (arep === brep) {
			return false;
		}

		if (this.preMergeCallback(a, b, simpleReason, lefts, rights) === "cancel") {
			return false;
		}

		const dependencies = [];
		for (let i = 0; i < lefts.length; i++) {
			dependencies.push({ left: lefts[i], right: rights[i] });
		}
		this.components.addCongruence(a, b, simpleReason, dependencies);

		const parent = this.components.representative(arep);
		if (parent !== arep && parent !== brep) {
			throw new Error("EGraph.merge: unexpected new representative");
		}
		const child = arep === parent ? brep : arep;
		this.tagTracker.mergeInto(child, parent);

		// Find all references of the child and process them with
		// updateFunctionRep
		const childReferences = this.references.get(child);
		for (const childReference of childReferences) {
			this.references.get(parent).add(childReference);
			this.updateFunctionRep(childReference);
		}

		return true;
	}

	updateCongruence(): boolean {
		let madeChanges = false;
		while (this.lazyCongruence.length !== 0) {
			const q = this.lazyCongruence;
			this.lazyCongruence = [];
			for (const e of q) {
				madeChanges = this.mergeApplications(e.left, e.right, null, e.leftOperands, e.rightOperands) || madeChanges;
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
			throw new Error("EGraph.explainCongruence: expected missing path");
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

	getClasses(duplicate?: boolean): Map<EObject, EClassDescription<Term>> {
		const mapping: Map<EObject, EClassDescription<Term>> = new Map();
		for (const [k, id] of this.tuples) {
			const representative = this.components.representative(id);
			let eclass = mapping.get(representative);
			if (eclass === undefined) {
				eclass = { members: [], representative };
				mapping.set(representative, eclass);
			}
			if (duplicate) {
				mapping.set(id, eclass);
			}
			const term = k[0];
			const operands = k.slice(1) as EObject[];
			eclass.members.push({ id, term, operands });
		}
		return mapping;
	}
}
