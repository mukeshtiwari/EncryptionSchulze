# -
# Required variables:
#JAVA_HOME="/usr/lib/jvm/java-8-openjdk-amd64/"
JAVA_HOME:="/opt/homebrew/Cellar/openjdk/17/libexec/openjdk.jdk/Contents/Home"
#
# Configs:
#  BUILD_DIR
#  TARGET_DIR
#  OCAMLFIND
#  JAVA_INCLUDES
#  JAVACFLAGS

BUILD_DIR = bin
TARGET_DIR = bin

T = $(TARGET_DIR)

TARGETS = \
	$(T)/camljava.cmxa $(T)/javacaml.cmxa \
	$(T)/ocaml-java-ppx $(T)/ocaml-java.jar

all: $(TARGETS)

export JAVA_INCLUDES = \
	-I $(JAVA_HOME)/include \
	-I $(JAVA_HOME)/include/linux \
	-I $(JAVA_HOME)/include/darwin

export CCLIBS = \
	-L $(JAVA_HOME)/jre/lib/amd64/server \
	-L $(JAVA_HOME)/jre/lib/server

MAKE_CAMLJAVA = make -f cmxa.Makefile \
		BUILD_DIR=$(BUILD_DIR)/camljava/build \
		TARGET_DIR=$(TARGET_DIR)/camljava \
		EXTRA_CCFLAGS="-DTARGET_CAMLJAVA"

MAKE_JAVACAML = make -f cmxa.Makefile \
		BUILD_DIR=$(BUILD_DIR)/javacaml/build \
		TARGET_DIR=$(TARGET_DIR)/javacaml \
		EXTRA_CCFLAGS="-DTARGET_JAVACAML -fPIC"

$(T)/camljava.cmxa:
	$(MAKE_CAMLJAVA) all

$(T)/javacaml.cmxa:
	$(MAKE_JAVACAML) all

MAKE_PPX = make -f ppx.Makefile \
		BUILD_DIR=$(BUILD_DIR)/ppx \
		TARGET_DIR=$(TARGET_DIR)

$(T)/ocaml-java-ppx:
	$(MAKE_PPX) $@

MAKE_JAR = make -f jar.Makefile \
		BUILD_DIR=$(BUILD_DIR)/jar \
		TARGET_DIR=$(TARGET_DIR) \

$(T)/ocaml-java.jar:
	$(MAKE_JAR) $@

clean:
	$(MAKE_CAMLJAVA) clean
	$(MAKE_JAVACAML) clean
	$(MAKE_JAR) clean

re: clean
	make all

.PHONY: all clean re $(TARGETS)
