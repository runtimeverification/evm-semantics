pipeline {
  agent {
    dockerfile {
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  stages {
    stage("Init title") {
      when { changeRequest() }
      steps {
        script {
          currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
        }
      }
    }
    stage("Install Z3") {
      steps {
        ansiColor('xterm') {
          sh '''
            mkdir scratch
            cd scratch
            git clone 'https://github.com/z3prover/z3'
            cd z3
            python scripts/mk_make.py --prefix=$HOME/.local
            cd build
            make -j4
            make install
            export PATH=$HOME/.local/bin:$PATH
            z3 --version
          '''
        }
      }
    }
    stage('Build and Test') {
      steps {
        ansiColor('xterm') {
          sh '''
            export PATH=$HOME/.local/bin:$PATH
            nprocs=$(nproc)
            [ "$nprocs" -gt '10' ] && nprocs='10'
            nprocs_proofs="$nprocs"
            [ "$nprocs_proofs" -gt '6' ] && nprocs_proofs='6'
            make deps        -B
            make build       -B -j"$nprocs"
            make split-tests -B -j"$nprocs"
            make test-concrete  -j"$nprocs"
            make test-proof     -j"$nprocs_proofs"
          '''
        }
      }
    }
  }
}
