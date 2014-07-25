FROM ubuntu
MAINTAINER Guillaume Claret

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y gcc make git

# OCaml
RUN apt-get install -y ocaml camlp4-extra

# Coq trunk
WORKDIR /root
RUN git clone https://github.com/coq/coq.git
WORKDIR /root/coq
RUN yes "" |./configure -no-native-compiler
RUN make -j4
RUN make install

# Containers library
RUN apt-get install -y wget
WORKDIR /root
RUN wget http://coq.inria.fr/pylons/contribs/files/Containers/trunk/Containers.tar.gz -O - |tar -xz
WORKDIR /root/Containers
RUN coq_makefile -f Make -o Makefile
RUN make
RUN make install

# Compile the project
ADD . /root/coq-labelled-containers
WORKDIR /root/coq-labelled-containers
CMD ./configure.sh && make