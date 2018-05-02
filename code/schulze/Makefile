%.class : %.java
	javac -cp ".:../javacryptocode/unicrypt-2.3/src/main/java:../javacryptocode/jna-gmp-jnagmp-parent-2.1.0/jnagmp/src/main/java:../javacryptocode/jna-4.5.1/src" $*.java

%.run: %.class
	java -cp ".:../javacryptocode/unicrypt-2.3/src/main/java:../javacryptocode/jna-gmp-jnagmp-parent-2.1.0/jnagmp/src/main/java:../javacryptocode/jna-4.5.1/dist/linux-x86-64.jar:../javacryptocode/jna-4.5.1/dist/jna.jar:../javacryptocode/jarfiles/jnagmp-2.0.0.jar" $*




