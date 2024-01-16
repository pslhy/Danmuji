(lang dune 2.0)

(name Danmuji)

(source
 (github pslhy/Danmuji))

(authors "@astean1001")

(maintainers "@astean1001")

(license GPL-3.0-or-later)

(documentation https://psl.hanyang.ac.kr)

(generate_opam_files true)

(package
 (name Danmuji)
 (synopsis "Daikon input file-compatible invariant detector")
 (description "Danmuji is an invariant detection tool designed for compatibility with Daikon input files. 
   It offers efficient analysis of program behaviors and automatic invariant inference, making it 
   an invaluable tool for software debugging and verification.")
 (depends
  (ocaml (>= 4.7.0))
  (dune (>= 2.9.0))
  batteries integers
 )
 (tags
  (invariant, program repair)
 )
)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
