" Vim indent script for Cure programming language
if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetCureIndent()
setlocal indentkeys=0{,0},0),0],0=else,0=elif,0=catch,0=finally,0=after,0=state,0=event,!^F,o,O

if exists("*GetCureIndent")
  finish
endif

function! GetCureIndent()
  let lnum = prevnonblank(v:lnum - 1)
  if lnum == 0
    return 0
  endif

  let prev_line = getline(lnum)
  let curr_line = getline(v:lnum)
  let ind = indent(lnum)

  " Increase indent after lines ending in or starting with block-opening keywords
  let block_openers = '\v^\s*(mod|fn|type|typealias|rec|interface|implementation|actor|sup|app|fsm|state|event|transition|match|pickup|if|elif|else|try|catch|finally|receive|after|on_transition|on_enter|on_exit|on_failure|on_timer)>|\=\s*$'
  if prev_line =~ block_openers
    let ind += shiftwidth()
  endif

  " Decrease indent for block Continuation/closing heads on current line
  let dedent_keywords = '\v^\s*(elif|else|catch|finally|after)>'
  if curr_line =~ dedent_keywords
    let ind -= shiftwidth()
  endif

  return ind < 0 ? 0 : ind
endfunction
