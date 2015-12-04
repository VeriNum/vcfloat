#!/bin/bash
#
# VCFloat: A Unified Coq Framework for Verifying C Programs with
# Floating-Point Computations. Application to SAR Backprojection.
# 
# Version 1.0 (2015-12-04)
# 
# Copyright (C) 2015 Reservoir Labs Inc.
# All rights reserved.
# 
# This file, which is part of VCFloat, is free software. You can
# redistribute it and/or modify it under the terms of the GNU General
# Public License as published by the Free Software Foundation, either
# version 3 of the License (GNU GPL v3), or (at your option) any later
# version. A verbatim copy of the GNU GPL v3 is included in gpl-3.0.txt.
# 
# This file is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE for
# more details about the use and redistribution of this file and the
# whole VCFloat library.
# 
# This work is sponsored in part by DARPA MTO as part of the Power
# Efficiency Revolution for Embedded Computing Technologies (PERFECT)
# program (issued by DARPA/CMO under Contract No: HR0011-12-C-0123). The
# views and conclusions contained in this work are those of the authors
# and should not be interpreted as representing the official policies,
# either expressly or implied, of the DARPA or the
# U.S. Government. Distribution Statement "A" (Approved for Public
# Release, Distribution Unlimited.)
# 
# 
# If you are using or modifying VCFloat in your work, please consider
# citing the following paper:
# 
# Tahina Ramananandro, Paul Mountcastle, Benoit Meister and Richard
# Lethin.
# A Unified Coq Framework for Verifying C Programs with Floating-Point
# Computations.
# In CPP (5th ACM/SIGPLAN conference on Certified Programs and Proofs)
# 2016.
# 
# 
# VCFloat requires third-party libraries listed in ACKS along with their
# copyright information.
# 
# VCFloat depends on third-party libraries listed in ACKS along with
# their copyright and licensing information.
#
# External libraries needed by our work:
# R-CoqLib, CompCert, Flocq and Coq-Interval
# and their dependencies
#
# We assume that Coq 8.5beta2 (with real numbers), git, wget, autoconf
# and automake are already installed and in the PATH. Nothing else is
# needed.
#
# NOTE: This script is not required to be run from the full-scale
# submission VM.  Everything is already installed and compiled.
#

# Get and build R-CoqLib
if [ ! -d rcoqlib ]
then
    git clone 'https://github.com/reservoirlabs/rcoqlib' rcoqlib || exit 1
    pushd rcoqlib || exit 1
    ./configure || exit 1
    make $* || exit 1
    popd || exit 1
fi

# Get CompCert Clight.
# NOTE: Since we are not compiling the whole CompCert,
# we do not need to use the copy of Flocq that is
# distributed with CompCert.

if [ ! -d compcert ]
then
    CC=compcert-2.4
    rm -rf $CC.tgz $CC compcert.aux
    git clone 'https://github.com/AbsInt/CompCert.git' $CC || exit 1
    mkdir compcert.aux || exit 1
    pushd $CC || exit 1
    git checkout 5dd15440 || exit 1 
    popd || exit 1
    cp -t compcert.aux $CC/{ia32/Archi,exportclight/Clightdefs,common/{AST,Errors,Events,Globalenvs,Memdata,Memory,Memtype,Smallstep,Values},cfrontend/{Clight,Cop,Ctypes},lib/{Axioms,Coqlib,Fappli_IEEE_extra,Floats,Integers,Intv,Maps}}.v || exit 1
    pushd compcert.aux || exit 1
    patch -p1 < ../patches/compcert.patch || exit 1 
    popd || exit 1
    rm -rf $CC
    mv compcert.aux compcert || exit 1
    true
else
    true
fi

# Get and build Ssreflect
SSR=ssreflect-1.5.coq85beta2
if [ ! -d ssreflect ]
then
    rm -rf $SSR.tar.gz $SSR
    wget "http://ssr.msr-inria.inria.fr/FTP/$SSR.tar.gz" || exit 1
    tar xf $SSR.tar.gz || exit 1
    rm -f $SSR.tar.gz
    mv $SSR ssreflect || exit 1
else
    true
fi
make -C ssreflect $* || exit 1

# Get and build MathComp
MC=mathcomp-1.5.coq85beta2
if [ ! -d mathcomp ]
then
    rm -rf $MC.tar.gz $MC
    wget "http://ssr.msr-inria.inria.fr/FTP/$MC.tar.gz"  || exit 1
    tar xf $MC.tar.gz  || exit 1
    rm -f $MC.tar.gz
    pushd $MC  || exit 1
    echo "-R ../ssreflect/theories Ssreflect" >> Make  || exit 1 
    echo "-I ../ssreflect/src" >> Make  || exit 1
    popd  || exit 1
    mv $MC mathcomp  || exit 1 
else
    true
fi
make -C mathcomp $*  || exit 1

# Get and build Flocq
if [ ! -d flocq ]
then
    rm -rf flocq.aux
    git clone 'https://gforge.inria.fr/git/flocq/flocq.git' flocq.aux  || exit 1
    pushd flocq.aux  || exit 1
    git checkout bcbcde24  || exit 1
    ./autogen.sh  || exit 1
    ./configure  || exit 1
    popd  || exit 1
    mv flocq.aux flocq || exit 1 
else
    true
fi
pushd flocq  || exit 1
./remake  || exit 1
popd  || exit 1

# Get and build Coq-Interval
if [ ! -d interval ]
then
    rm -rf interval.aux
    git clone https://scm.gforge.inria.fr/anonscm/git/coq-interval/coq-interval.git interval.aux || exit 1 
    pushd interval.aux  || exit 1
    git checkout 81f1f918  || exit 1
    patch -p1 < ../patches/interval.patch || exit 1 
    ./autogen.sh  || exit 1
COQC='coqc -R ../flocq/src Flocq -I ../ssreflect/src -R ../ssreflect/theories Ssreflect -R ../mathcomp/theories MathComp' ./configure || exit 1 
    popd  || exit 1
    mv interval.aux interval || exit 1 
else
    true
fi
pushd interval  || exit 1
./remake  || exit 1
popd  || exit 1

# Everything is installed. Disable this file
chmod -x $0  || exit 1
