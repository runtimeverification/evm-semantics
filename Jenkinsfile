pipeline {
  agent {
    dockerfile {
      label 'proofs'
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
            make deps        -B
            make build       -B -j4
            make split-tests -B
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
              dir('mantis-cardano') {
                git credentialsId: 'rv-jenkins', url: 'git@github.com:input-output-hk/mantis-cardano.git', branch: 'fix-master/GMC-136-round_3'
              }
              sh '''
                export PATH=$HOME/.local/bin:$PATH
                export LD_LIBRARY_PATH=$(pwd)/.build/local/lib
                cd mantis-cardano
                git submodule update --init
                sbt dist
                sbt -Dmantis.vm.external.vm-type="kevm" -Dmantis.vm.external.executable-path="../.build/vm/kevm-vm" 'ets:testOnly *BlockchainSuite -- -Dexg=bcExploitTest/DelegateCallSpam,GeneralStateTests/stQuadraticComplexityTest/*'
              '''
            }
          }
        }
      }
    }
  }
}
