.DUMMY: all clean

COQ_FILES=alloy.v alloy_util.v case.v compile_src11_ptx.v

CLASSPATH=.:./alloy4.2.jar

JAVAFLAGS=

all: src11_ptx.vo

src11_ptx.vo: $(patsubst %.v,%.vo,$(COQ_FILES))

%.vo: %.v
	coqc $<

compile_src11_ptx.v: Alloqc.class util.als ptx.als src11.als compile_src11_ptx.als
	./alloqc.sh compile_src11_ptx.als

Alloqc.class : Alloqc.java
	javac $(JAVAFLAGS) -classpath alloy4.2.jar Alloqc.java

RunAlloy.class: RunAlloy.java
	javac $(JAVAFLAGS) -classpath alloy4.2.jar RunAlloy.java

clean:
	rm -f *.glob *.vo *.class compile_src11_ptx.vo

src11_4: RunAlloy.class
	time java -cp $(CLASSPATH) RunAlloy -f compile_src11_ptx.als -b 4 src11_ptx_legal_coherence
	time java -cp $(CLASSPATH) RunAlloy -f compile_src11_ptx.als -b 4 src11_ptx_legal_atomicity
	time java -cp $(CLASSPATH) RunAlloy -f compile_src11_ptx.als -b 4 src11_ptx_legal_sc

src11_5: RunAlloy.class
	time java -cp $(CLASSPATH) RunAlloy -f compile_src11_ptx.als -b 5 src11_ptx_legal_coherence
	time java -cp $(CLASSPATH) RunAlloy -f compile_src11_ptx.als -b 5 src11_ptx_legal_atomicity
	time java -cp $(CLASSPATH) RunAlloy -f compile_src11_ptx.als -b 5 src11_ptx_legal_sc
