" Filetype detection for Cure (.cure)
augroup cure_ftdetect
  autocmd!
  autocmd BufNewFile,BufRead *.cure setfiletype cure
augroup END
