// Live syntax highlighting for the playground editor.
//
// It runs the same tree-sitter grammar and `highlights.scm` the editor
// plugins use (tree-sitter-cure, neovim-cure, zed-cure), so the playground
// colours code exactly like an editor does. The grammar is compiled to
// `vendor/tree-sitter-cure.wasm` with `mix assets.grammar`.
//
// The editor is a transparent <textarea> laid over a <pre> holding the
// highlighted copy of its text: the textarea keeps native editing, the pre
// shows the colours.

import {Parser, Language, Query} from "web-tree-sitter"
import runtimeWasm from "web-tree-sitter/web-tree-sitter.wasm"
import cureWasm from "../vendor/tree-sitter-cure.wasm"
import highlightsScm from "../../../tree-sitter-cure/queries/highlights.scm"

// Capture names map onto the Makeup token classes the site already styles
// (see `.makeup` in app.css), so the playground follows the site's theme.
// The longest matching prefix wins: `keyword.function` -> `keyword`.
const CAPTURE_CLASSES = {
  "keyword": "k",
  "type": "nc",
  "constructor": "nc",
  "title": "nc",
  "function": "nf",
  "variable": "n",
  "variable.special": "ni",
  "property": "n",
  "label": "na",
  "attribute": "na",
  "boolean": "kc",
  "constant.builtin": "kc",
  "number": "m",
  "string": "s",
  "string.special": "sc",
  "string.special.symbol": "ss",
  "string.regex": "sr",
  "string.escape": "se",
  "embedded": "n",
  "comment": "c",
  "operator": "o",
  "punctuation": "p",
  "punctuation.special": "se",
}

const classFor = name => {
  const parts = name.split(".")
  for (let n = parts.length; n > 0; n--) {
    const cls = CAPTURE_CLASSES[parts.slice(0, n).join(".")]
    if (cls) return cls
  }
  return null
}

const escapeHtml = text =>
  text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")

let highlighterPromise = null

const loadHighlighter = () => {
  highlighterPromise ||= (async () => {
    await Parser.init({locateFile: () => runtimeWasm})
    const language = await Language.load(cureWasm)
    const parser = new Parser()
    parser.setLanguage(language)
    const query = new Query(language, highlightsScm)
    return {parser, query}
  })()
  return highlighterPromise
}

// Paint each character with the class of the innermost capture covering it.
// Wider captures are painted first so nested ones (an interpolation inside a
// string) land on top; among captures of the same node the later pattern
// wins, which is how highlights.scm expects to be read.
const highlight = ({parser, query}, source) => {
  const tree = parser.parse(source)
  const classes = new Array(source.length).fill(null)

  const captures = query
    .captures(tree.rootNode)
    .filter(({name}) => !name.startsWith("_"))
    .map(({name, patternIndex, node}) => ({
      cls: classFor(name),
      start: node.startIndex,
      end: node.endIndex,
      patternIndex,
    }))
    .filter(({cls}) => cls)
    .sort((a, b) => (b.end - b.start) - (a.end - a.start) || a.patternIndex - b.patternIndex)

  tree.delete()

  for (const {cls, start, end} of captures) classes.fill(cls, start, end)

  let html = ""
  for (let i = 0; i < source.length;) {
    let j = i + 1
    while (j < source.length && classes[j] === classes[i]) j++
    const text = escapeHtml(source.slice(i, j))
    html += classes[i] ? `<span class="${classes[i]}">${text}</span>` : text
    i = j
  }

  // A trailing newline would otherwise collapse in the <pre>, leaving it one
  // line shorter than the textarea.
  return html + " "
}

export const CureEditor = {
  mounted() {
    this.textarea = this.el.querySelector("textarea")
    this.code = this.el.querySelector("pre code")
    this.pre = this.code.parentElement
    this.gutter = this.el.querySelector(".cure-editor-gutter")

    this.syncScroll = () => {
      this.pre.scrollTop = this.gutter.scrollTop = this.textarea.scrollTop
      this.pre.scrollLeft = this.textarea.scrollLeft
    }
    this.render = () => {
      if (!this.highlighter) return
      const source = this.textarea.value
      this.code.innerHTML = highlight(this.highlighter, source)
      const lines = source.split("\n").length
      this.gutter.textContent = Array.from({length: lines}, (_, i) => i + 1).join("\n") + "\n "
      this.syncScroll()
    }
    // Tab indents instead of leaving the editor. insertText keeps undo intact.
    this.onKeydown = event => {
      if (event.key !== "Tab" || event.shiftKey || event.ctrlKey || event.metaKey || event.altKey) return
      event.preventDefault()
      document.execCommand("insertText", false, "  ")
    }

    this.textarea.addEventListener("input", this.render)
    this.textarea.addEventListener("scroll", this.syncScroll)
    this.textarea.addEventListener("keydown", this.onKeydown)

    loadHighlighter()
      .then(highlighter => {
        this.highlighter = highlighter
        this.render()
        this.el.classList.add("cure-editor-ready")
      })
      .catch(error => console.warn("Cure highlighting unavailable:", error))
  },
}
