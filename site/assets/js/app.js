// If you want to use Phoenix channels, run `mix help phx.gen.channel`
// to get started and then uncomment the line below.
// import "./user_socket.js"

// You can include dependencies in two ways.
//
// The simplest option is to put them in assets/vendor and
// import them using relative paths:
//
//     import "../vendor/some-package.js"
//
// Alternatively, you can `npm install some-package --prefix assets` and import
// them using a path starting with the package name:
//
//     import "some-package"
//
// If you have dependencies that try to import CSS, esbuild will generate a separate `app.css` file.
// To load it, simply add a second `<link>` to your `root.html.heex` file.

// Include phoenix_html to handle method=PUT/DELETE in forms and buttons.
import "phoenix_html"
import {Socket} from "phoenix"
import {LiveSocket} from "phoenix_live_view"
// yeesh 0.8.0 uses the phoenix-colocated mechanism: <yeesh-terminal> is a
// self-registering Lit Web Component, so no explicit hook entry is needed.
import "phoenix-colocated/yeesh"
import topbar from "../vendor/topbar"
import {CureEditor} from "./cure_editor"
// KaTeX typesets the TeX that `CureSite.MarkdownConverter` leaves in the
// markup. Its stylesheet is pulled in from assets/css/app.css and its web
// fonts are staged by `mix katex.fonts`.
import katex from "katex"

const csrfToken = document.querySelector("meta[name='csrf-token']").getAttribute("content")
const liveSocket = new LiveSocket("/live", Socket, {
  longPollFallbackMs: 2500,
  params: {_csrf_token: csrfToken},
  hooks: {CureEditor},
})

topbar.config({barColors: {0: "#29d"}, shadowColor: "rgba(0, 0, 0, .3)"})
window.addEventListener("phx:page-loading-start", _info => topbar.show(300))
window.addEventListener("phx:page-loading-stop", _info => topbar.hide())

liveSocket.connect()
window.liveSocket = liveSocket

if (process.env.NODE_ENV === "development") {
  window.addEventListener("phx:live_reload:attached", ({detail: reloader}) => {
    reloader.enableServerLogs()

    let keyDown
    window.addEventListener("keydown", e => keyDown = e.key)
    window.addEventListener("keyup", _e => keyDown = null)
    window.addEventListener("click", e => {
      if(keyDown === "c"){
        e.preventDefault()
        e.stopImmediatePropagation()
        reloader.openEditorAtCaller(e.target)
      } else if(keyDown === "d"){
        e.preventDefault()
        e.stopImmediatePropagation()
        reloader.openEditorAtDef(e.target)
      }
    }, true)

    window.liveReloader = reloader
  })
}


// Handle flash close
document.querySelectorAll("[role=alert][data-flash]").forEach((el) => {
  el.addEventListener("click", () => {
    el.setAttribute("hidden", "")
  })
})

// Standard Library interactive filter & '/' hotkey
const setupStdlibFilter = () => {
  const filterInput = document.getElementById("stdlib-filter")
  if (!filterInput) return

  const onInput = () => {
    const query = filterInput.value.toLowerCase().trim()

    // Filter sidebar list items and sections
    document.querySelectorAll("aside section").forEach((section) => {
      let hasVisibleLi = false
      section.querySelectorAll("li").forEach((li) => {
        const text = li.textContent.toLowerCase()
        if (query === "" || text.includes(query)) {
          li.style.display = ""
          hasVisibleLi = true
        } else {
          li.style.display = "none"
        }
      })
      section.style.display = query === "" || hasVisibleLi ? "" : "none"
    })

    // Filter index page grid cards
    document.querySelectorAll("article section").forEach((section) => {
      const cards = section.querySelectorAll(".grid > a")
      if (cards.length > 0) {
        let hasVisibleCard = false
        cards.forEach((card) => {
          const text = card.textContent.toLowerCase()
          if (query === "" || text.includes(query)) {
            card.style.display = ""
            hasVisibleCard = true
          } else {
            card.style.display = "none"
          }
        })
        section.style.display = query === "" || hasVisibleCard ? "" : "none"
      }
    })
  }

  filterInput.addEventListener("input", onInput)

  window.addEventListener("keydown", (e) => {
    if (
      e.key === "/" &&
      document.activeElement !== filterInput &&
      !["INPUT", "TEXTAREA"].includes(document.activeElement.tagName)
    ) {
      e.preventDefault()
      filterInput.focus()
    }
  })
}

// Math typesetting.
//
// `CureSite.MarkdownConverter` enables comrak's math extensions, so TeX
// written as `$x^2$`, `$$x^2$$`, `` $`x^2`$ `` or a ```math fence reaches
// the browser untouched, wrapped in `data-math-style="inline|display"`:
//
//   <span data-math-style="inline">\Pi</span>
//   <span data-math-style="display">a^2 + b^2 = c^2</span>
//   <code data-math-style="inline">\sqrt{3}</code>
//   <pre><code data-math-style="display">\sum_{i=0}^n i</code></pre>
//
// Each of those is replaced here by the KaTeX rendering. Elements that fail
// to render keep their literal TeX so the page degrades to readable source
// instead of an empty gap.
const MATH_SELECTOR = "[data-math-style]:not([data-math-rendered])"

const renderMathElement = (el) => {
  const display = el.dataset.mathStyle === "display"
  // A ```math fence arrives as <pre><code>: the whole <pre> has to go,
  // otherwise KaTeX would render inside a `white-space: pre` monospace box.
  const replaceable =
    el.tagName === "CODE" && el.parentElement && el.parentElement.tagName === "PRE"
      ? el.parentElement
      : el

  const tex = el.textContent
  const host = document.createElement("span")
  host.className = display ? "cure-math cure-math-display" : "cure-math"
  host.setAttribute("data-math-rendered", "")

  try {
    katex.render(tex, host, {
      displayMode: display,
      // Render both HTML and MathML: the former is what the KaTeX fonts
      // style, the latter is what screen readers and copy-paste pick up.
      output: "htmlAndMathml",
      // Never blow up a whole page over one bad formula; KaTeX inlines the
      // offending source in red instead.
      throwOnError: false,
      strict: "ignore",
      trust: false,
    })
  } catch (error) {
    console.error("[katex] could not render", tex, error)
    el.setAttribute("data-math-rendered", "")
    return
  }

  replaceable.replaceWith(host)
}

const renderMath = (root = document) => {
  root.querySelectorAll(MATH_SELECTOR).forEach(renderMathElement)
}

// Re-run after live navigation, which swaps in markup the initial pass never
// saw.
window.addEventListener("phx:page-loading-stop", () => renderMath())

const onReady = (fn) => {
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", fn)
  } else {
    fn()
  }
}

onReady(setupStdlibFilter)
onReady(() => renderMath())
