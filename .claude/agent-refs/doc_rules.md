# Doc-comment rules for McTT (`theories/`, branch ext/params-as-locals)

The coqdoc pages are published at https://hustmphrrr.github.io/McTT/. The docs
must read as external documentation of the library *as it is*.

## Content
1. External-facing. Never mention any of the following:
   - development stages, plans, history or alternatives ("option A/B/C",
     "the port", "now", "previously", "the old …", "we changed", "for now",
     "until …");
   - branches or commits;
   - AGENT/ notes, doc/alignment.md, or "the design document".

   State what a definition is, and what a theorem says or is for.
2. Concise. Use complete sentences, shorter than now wherever possible. Cut:
   - restatements of what the code plainly says;
   - hedging;
   - repetition across neighbouring comments.

   Keep the content a reader needs:
   - what each parameter or index means;
   - the invariant;
   - why a non-obvious premise is there;
   - a short example where one already exists.
3. Keep the existing coqdoc section headings (`(** * …`, `(** ** …`,
   `(** *** …`) and their structure.
4. Keep `REVISIT` markers, but phrase them as one plain sentence each.
5. Never add a comment where none exists. You may delete a comment that is
   purely development-stage talk. Plain `(* … *)` comments inside proofs:
   only remove stage talk from them; otherwise leave them alone.

## coqdoc formatting (this is what renders badly today)
- Multi-line displays of code, either surface syntax or Rocq terms, go in
  `<<` and `>>`, each on its own line at column 0. They render as `<pre>`.
  Indented text outside such a block is reflowed into the paragraph, which
  is the bug you are fixing.
- Inline code is `[x]`. Surface syntax inline is also `[…]`.
- Lists use `-` items, with a blank line before the list. Indent
  continuation lines under the item text. Nested lists indent further.
- Paragraphs are separated by blank lines.
- There is no bold. `*word*` renders literally, so drop it or rephrase.
  `_word_` is emphasis; use it sparingly.
- Don't use markdown tables or headings like `##` inside comments.

## Hard constraints
- **Code must be byte-for-byte unchanged outside comments.** After editing,
  run `python3 /tmp/code_unchanged.py <repo-relative paths…>` from anywhere.
  It compares each file with HEAD, ignoring comments and whitespace, and must
  print `ok`.
- Check the rendering of a few files you changed:
  `mkdir -p /tmp/cd-$USER-<group> && coqdoc --html --parse-comments --no-index -d /tmp/cd-$USER-<group> <file.v>`.
  Then inspect the HTML for `<pre>` blocks and `<ul class="doclist">`.
- Do not build the project, commit, or edit files outside your assigned set.
  Other agents are editing other files in the same checkout at the same time.
- Do not touch generated `theories/Frontend/Parser.v`, or `rocq_mcp_cache_*.v`.
