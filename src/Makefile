include ../opts.mk

SRC=archi.ml ast.ml builtins.ml config.ml cfg_constprop.ml cfg_dead_assign.ml	\
cfg.ml cfg_print.ml cfg_gen.ml cfg_liveness.ml cfg_nop_elim.ml cfg_run.ml			\
elang.ml elang_print.ml elang_gen.ml elang_run.ml e_regexp.ml									\
generated_parser.ml lexer_generator.ml linear_dse.ml linear_liveness.ml				\
linear.ml linear_print.ml linear_gen.ml linear_run.ml ltl.ml ltl_print.ml			\
ltl_gen.ml ltl_run.ml ltl_debug.ml main.ml options.ml parser.ml prog.ml				\
regalloc.ml report.ml riscv.ml rtl.ml rtl_print.ml rtl_gen.ml rtl_run.ml			\
symbols.ml tokenize.ml utils.ml

TG = main.exe

PROF:=$(if $(PROF),-ocamlopt ocamloptp,)

all: $(TG)

$(TG): $(SRC)
	dune build $(TG)
	# ocamlbuild $(PROF) -cflags  -warn-error,"+a-26" -cflags -w,"-26" -menhir "menhir --unused-tokens" -use-ocamlfind $(TG)

test_lexer: archi.ml config.ml e_regexp.ml lexer_generator.ml symbols.ml test_lexer.ml utils.ml
	dune exec ./test_lexer.exe
	dot -Tsvg /tmp/dfa.dot -o /tmp/dfa.svg
	dot -Tsvg /tmp/nfa.dot -o /tmp/nfa.svg

config.ml: ../configure ../opts.mk
	cd .. && ./configure ${CONF_OPTS}

clean:
	dune clean
	rm -f config.ml
