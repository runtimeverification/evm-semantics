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
    stage('Build') {
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
          '''
        }
      }
    }
    stage('Test') {
      parallel {
        stage('Conformance') {
          steps {
            ansiColor('xterm') {
              sh '''
                export PATH=$HOME/.local/bin:$PATH
                nprocs=$(nproc)
                [ "$nprocs" -gt '10' ] && nprocs='10'
                make test-concrete -j"$nprocs"
              '''
            }
          }
        }
        stage('Proofs') {
          steps {
            ansiColor('xterm') {
              sh '''
                export PATH=$HOME/.local/bin:$PATH
                nprocs=$(nproc)
                [ "$nprocs" -gt '6' ] && nprocs='6'
                make test-proof -j"$nprocs"
              '''
            }
          }
        }
        stage('Mantis') {
          steps {
            ansiColor('xterm') {
              sh '''
                export PATH=$HOME/.local/bin:$PATH
                export LD_LIBRARY_PATH=$(pwd)/.build/local/lib
                rm -rf mantis-cardano
                git clone 'git@github.com:input-output-hk/mantis-cardano'
                cd mantis-cardano
                git checkout fix-master/GMC-136-round_3
                git submodule update --init
                sbt dist
                sbt -Dmantis.vm.external.vm-type="kevm" -Dmantis.vm.external.executable-path="../evm-semantics/.build/vm/kevm-vm" 'ets:testOnly *BlockchainSuite -- -Dexg=bcExploitTest/DelegateCallSpam,GeneralStateTests/stQuadraticComplexityTest/*'
              '''
            }
          }
        }
      }
    }
  }
}
