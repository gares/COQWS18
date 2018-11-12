COQC=coqc
MC=
WEB=/media/sophia/www-sop/teams/marelle/coq-18/

VS=$(filter-out %tmp.v,$(filter-out %-todo.v,$(wildcard *.v)))
EX=$(filter-out %tmp.v,$(filter-out %-todo.v,$(wildcard exercise*.v)))
FILES=$(VS:%.v=%.html) $(VS) $(EX:%.v=%-todo.v) $(EX:%.v=%-solution.html)

all: jscoq udoc/udoc.byte cheat-sheet/cheatsheet.pdf $(FILES)

jscoq: jscoq.tgz
	tar -xzf jscoq.tgz
	touch jscoq
	cd jscoq/coq-js; ln -sf ../coq-pkgs .
	echo '#document { max-width: 50em; width: 100% }' >> jscoq/ui-css/jscoq.css
	sed -i 's/width: 51em;/max-width: 51em;/' jscoq/ui-css/coq-base.css

udoc/udoc.byte: udoc.patch
	$(MAKE) check-ocaml-ver-4.02.0
	rm -rf udoc
	git clone https://github.com/ejgallego/udoc.git
	cd udoc && git checkout ff209e2ba83e7472cd4da8f2adf5f9a09a55de2f
	cd udoc && patch -p1 < ../udoc.patch
	cd udoc && make

cheat-sheet/cheatsheet.pdf: cheat-sheet/cheatsheet.tex
	make -C cheat-sheet

check-ocaml-ver-%:
	@ V=`(echo -n '2 '; ocamlc -version; echo -n '1 '; echo $*) \
	  | sed 's/\./ /g' \
	  | sort -n -k 4 -k 3 -k 2 -k 1 | head -n 1 | cut -d ' ' -f 1)`; \
	if `test $$V = 2`; then echo "OCaml must be >= $*"; false; fi

upload: $(FILES) cheat-sheet/cheatsheet.pdf jscoq.tgz
	mkdir -p $(WEB)
	[ -d $(WEB)/jscoq ] || cp -ra jscoq $(WEB)
	cp $(FILES) FileSaver.js Blob.js local.css cheat-sheet/cheatsheet.pdf \
		$(WEB)

%.html.tmp: %.v header footer Makefile udoc/udoc.byte
	@cat header $< footer > $*tmp.v
	@# if does not work, then html ok but no links
	-$(COQC) -w -notation-overridden,-undo-batch-mode $*tmp.v > /dev/null
	@./udoc/udoc.byte -t $* $*tmp.v -o $@
	@sed -i -e 's?^ *<h1>$*tmp</h1>??' $@
	@sed -i -e 's?^ *<title.*?<title>$*</title>?' $@
	@sed -i -e 's?^ *<h1>$*</h1>??' $@
	@sed -i -e 's?</head>?<link rel="stylesheet" href="local.css" /></head>?' $@
	@sed -i -e 's?</title>?</title><script src="Blob.js" type="text/javascript"></script>?' $@
	@sed -i -e 's?</title>?</title><script src="FileSaver.js" type="text/javascript"></script>?' $@
	@rm -f $<.tmp

run: jscoq
	@echo "Go to: http://localhost:8000/lesson1.html"
	python3 -m http.server 8000 || python -m SimpleHTTPServer 8000

validate: $(VS) $(EX) test.v
	for x in $^; do $(COQC) $$x || exit 1; done

# Lessons
lesson%.html: lesson%.html.tmp
	@mv $< $@

# test
test.html: test.html.tmp
	@mv $< $@
	
# Exercises
exercise%.html: exercise%.html.tmp
	@sed -e '/^(\*D\*).*$$/d' -e 's/^(\*A\*).*$$/Admitted./' -e 's/^(\*a\*).*$$/  admit./'  $< > $@
exercise%-solution.html: exercise%.html.tmp
	@cp $< $@
exercise%-todo.v: exercise%.v
	@sed -e '/^(\*D\*).*$$/d' -e 's/^(\*A\*).*$$/Admitted./' -e 's/^(\*a\*).*$$/  admit./'  $< > $@
