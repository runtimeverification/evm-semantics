pipeline {
  agent none
  options {
    ansiColor('xterm')
  }
  stages {
    stage("Init title") {
      when {
        changeRequest()
        beforeAgent true
      }
      steps {
        script {
          currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
        }
      }
    }
    stage('Build and Test') {
      when {
        changeRequest()
        beforeAgent true
      }
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          args '-m 60g'
        }
      }
      stages {
        stage('Dependencies') {
          steps {
            sh '''
              make all-deps -B
              make split-tests -B
            '''
          }
        }
        stage('Build') {
          steps {
            sh '''
              make build build-llvm build-haskell build-node -j4 -B
            '''
          }
        }
        stage('Test Execution') {
          failFast true
          parallel {
            stage('Conformance (OCaml)') {
              steps {
                sh '''
                  nprocs=$(nproc)
                  [ "$nprocs" -gt '16' ] && nprocs='16'
                  make test-conformance -j"$nprocs" TEST_CONCRETE_BACKEND=ocaml
                '''
              }
            }
            stage('Conformance (LLVM)') {
              steps {
                sh '''
                  nprocs=$(nproc)
                  [ "$nprocs" -gt '16' ] && nprocs='16'
                  make test-conformance -j"$nprocs" TEST_CONCRETE_BACKEND=llvm
                '''
              }
            }
          }
        }
        stage('Test Proofs (Java)') {
          options {
            lock("proofs-${env.NODE_NAME}")
          }
          steps {
            sh '''
              nprocs=$(nproc)
              [ "$nprocs" -gt '6' ] && nprocs='6'
              make test-proof -j"$nprocs"
            '''
          }
        }
        stage('Test Interactive') {
          failFast true
          parallel {
            stage('OCaml krun') {
              steps {
                sh '''
                  make test-interactive-run TEST_CONCRETE_BACKEND=ocaml
                '''
              }
            }
            stage('LLVM krun') {
              steps {
                sh '''
                  make test-interactive-run TEST_CONCRETE_BACKEND=llvm
                '''
              }
            }
            stage('Java krun') {
              steps {
                sh '''
                  make test-interactive-run TEST_CONCRETE_BACKEND=java
                '''
              }
            }
            stage('Haskell krun') {
              steps {
                sh '''
                  make test-interactive-run TEST_CONCRETE_BACKEND=haskell
                '''
              }
            }
            stage('OCaml kast') {
              steps {
                sh '''
                  make test-parse TEST_CONCRETE_BACKEND=ocaml
                '''
              }
            }
            stage('Failing tests') {
              steps {
                sh '''
                  make test-failure TEST_CONCRETE_BACKEND=ocaml
                  make test-failure TEST_CONCRETE_BACKEND=llvm
                '''
              }
            }
            stage('Java KLab') {
              steps {
                sh '''
                  make test-klab-prove TEST_SYMBOLIC_BACKEND=java
                '''
              }
            }
            stage('Haskell Search') {
              steps {
                sh '''
                  make test-interactive-search TEST_SYMBOLIC_BACKEND=haskell -j4
                '''
              }
            }
            stage('KEVM help') {
              steps {
                sh '''
                  ./kevm help
                '''
              }
            }
          }
        }
      }
    }
    stage('Deploy') {
      when {
        not { changeRequest() }
        branch 'master'
        beforeAgent true
      }
      agent { label 'docker' }
      options { skipDefaultCheckout() }
      environment {
        GITHUB_TOKEN    = credentials('rv-jenkins')
        KEVM_RELEASE_ID = '1.0.0'
      }
      stages {
        stage('Checkout SCM') {
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              checkout scm
              script {
                env.K_RELEASE = sh(script: 'cat deps/k_release', returnStdout: true).trim()
              }
            }
          }
        }
        stage('Build Ubuntu Bionic Package') {
          agent {
            dockerfile {
              dir "kevm-${env.KEVM_RELEASE_ID}/package"
              filename 'Dockerfile.ubuntu-bionic'
              additionalBuildArgs "--build-arg USER_ID=\$(id -u) --build-arg GROUP_ID=\$(id -g) --build-arg K_RELEASE=${env.K_RELEASE}"
              reuseNode true
            }
          }
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              sh '''
                sudo apt-get update && sudo apt-get upgrade --yes
                cp -r package/debian ./
                dpkg-buildpackage --no-sign
              '''
            }
            stash name: 'bionic', includes: "kevm_${env.KEVM_RELEASE_ID}_amd64.deb"
          }
        }
        stage('Test Ubuntu Bionic Package') {
          agent {
            dockerfile {
              dir "kevm-${env.KEVM_RELEASE_ID}/package"
              filename 'Dockerfile.ubuntu-bionic'
              additionalBuildArgs "--build-arg USER_ID=\$(id -u) --build-arg GROUP_ID=\$(id -g) --build-arg K_RELEASE=${env.K_RELEASE}"
              reuseNode true
            }
          }
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              unstash 'bionic'
              sh '''
                sudo apt-get update && sudo apt-get upgrade --yes
                sudo apt-get install ./kevm_${KEVM_RELEASE_ID}_amd64.deb
                make test-interactive-firefly
              '''
            }
          }
        }
        stage('Build Arch Package') {
          agent {
            dockerfile {
              dir "kevm-${env.KEVM_RELEASE_ID}/package"
              filename 'Dockerfile.arch'
              additionalBuildArgs "--build-arg USER_ID=\$(id -u) --build-arg GROUP_ID=\$(id -g) --build-arg K_RELEASE=${env.K_RELEASE}"
              reuseNode true
            }
          }
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              sh '''
                sudo pacman -Syu --noconfirm
                cd package
                makepkg --noconfirm --syncdeps
              '''
            }
            stash name: 'arch', includes: "kevm-${env.KEVM_RELEASE_ID}/package/kevm-git-${env.KEVM_RELEASE_ID}-1-x86_64.pkg.tar.xz"
          }
        }
        stage('Test Arch Package') {
          agent {
            dockerfile {
              dir "kevm-${env.KEVM_RELEASE_ID}/package"
              filename 'Dockerfile.arch'
              additionalBuildArgs "--build-arg USER_ID=\$(id -u) --build-arg GROUP_ID=\$(id -g) --build-arg K_RELEASE=${env.K_RELEASE}"
              reuseNode true
            }
          }
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              unstash 'arch'
              sh '''
                sudo pacman -Syu --noconfirm
                sudo pacman --noconfirm -U kevm-git-${KEVM_RELEASE_ID}-1-x86_64.pkg.tar.xz
                make test-interactive-firefly
              '''
            }
          }
        }
        stage('Upload Packages') {
          agent {
            dockerfile {
              dir "kevm-${env.KEVM_RELEASE_ID}/package"
              filename 'Dockerfile.arch'
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
              reuseNode true
            }
          }
          steps {
            unstash 'bionic'
            unstash 'arch'
            sh '''
              git_commit=$(cd kevm-$KEVM_RELEASE_ID && git rev-parse --short HEAD)
              hub release create                                                                                                      \
                  --attach "kevm_${KEVM_RELEASE_ID}_amd64.deb#Ubuntu Bionic (18.04) Package"                                          \
                  --attach "kevm-${KEVM_RELEASE_ID}/package/kevm-git-${KEVM_RELEASE_ID}-1-x86_64.pkg.tar.xz#Arch Package"             \
                  --message "$(echo -e "KEVM Release $KEVM_RELEASE_ID - $git_commit\n\n" ; cat kevm-${KEVM_RELEASE_ID}/INSTALL.md ;)" \
                  --commitish $(git rev-parse HEAD) "v$KEVM_RELEASE_ID-$git_commit"
            '''
          }
        }
      }
      post {
        failure {
          slackSend color: '#cb2431'                                   \
                  , channel: '#kevm'                                   \
                  , message: "KEVM Packaging Failed: ${env.BUILD_URL}"
        }
      }
    }
  }
}
