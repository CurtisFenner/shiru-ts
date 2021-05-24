interface MapConstructor {
	/// The built-in `MapConstructor` gives a type of `Map<any, any>` to
	/// `new Map()`, which is dangerous.
	new <K = unknown, V = unknown>(): Map<K, V>;
}
