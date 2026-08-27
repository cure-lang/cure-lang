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

const csrfToken = document.querySelector("meta[name='csrf-token']").getAttribute("content")
const liveSocket = new LiveSocket("/live", Socket, {
  longPollFallbackMs: 2500,
  params: {_csrf_token: csrfToken},
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

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", setupStdlibFilter)
} else {
  setupStdlibFilter()
}