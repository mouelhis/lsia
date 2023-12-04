clear: rm -f lsia *~ #*# *.cmo *.cmi *.mli
SOURCES = toolkit.ml common.ml parse_tree.ml lsiapar.mly lsialex.mll datastructs.ml automaton.ml ptree_to_sia.ml string_print_ds.ml main.ml
RESULT  = lsia
LIBS = unix str
all: debug-code
-include OCamlMakefile