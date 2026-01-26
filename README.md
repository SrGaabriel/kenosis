# 🕊️ kenosis

Kenosis is a simple and lightweight serialization/deserialization library for Lean 4. It is written to be ergonomic, generic, and extensible. Kenosis plans to support a variety of serialization formats, including but not limited to JSON, TOML, and binary formats.

# 🎨 Features

- [x] Tree-based serialization (aeson-style)
- [x] Generic and extensible
- [x] Derived instances for user-defined types
- [x] JSON support (encoding and decoding)
- [x] Binary serialization (LEB128 varint encoding)
- [x] TOML support (encoding and decoding)
- [x] Monadic deserializing
- [x] Unified Serialize/Deserialize typeclasses (format-agnostic)
- [ ] More flexible serialization (serial names, skipping fields, etc.)
- [ ] Configurable rendering
- [ ] Little-endian binary variants
- [ ] Streaming/incremental parsing for large inputs

# ✨ Etymology

Kenosis comes from the Greek word kenóō, meaning “to empty.” In the context of serialization, it evokes the idea of reducing an object to its essential form, stripping away runtime behavior and context so that its core data can be stored or transmitted. Deserialization then reconstructs the object from this essential representation, allowing it to be used again in memory.