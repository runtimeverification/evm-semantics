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
              make build build-llvm build-haskell build-node -j4
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
              make test-prove -j"$nprocs"
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
    stage('Release') {
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
        stage('Checkout SCM - Download K Release') {
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              checkout scm
              sh '''
                commit_short=$(cd deps/k && git rev-parse --short HEAD)
                K_RELEASE="https://github.com/kframework/k/releases/download/nightly-$commit_short"
                curl --fail --location "${K_RELEASE}/kframework_5.0.0_amd64_bionic.deb"    --output kframework.deb
                curl --fail --location "${K_RELEASE}/kframework-5.0.0-1-x86_64.pkg.tar.xz" --output kframework-git.pkg.tar.xz
              '''
              stash name: 'bionic-kframework', includes: 'kframework.deb'
              stash name: 'arch-kframework',   includes: 'kframework-git.pkg.tar.xz'
            }
          }
        }
        stage('Build Source Tarball') {
          agent {
            dockerfile {
              dir "kevm-${env.KEVM_RELEASE_ID}/package"
              filename 'Dockerfile.arch'
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
              reuseNode true
            }
          }
          steps {
            dir("kevm-${KEVM_RELEASE_ID}-src") {
              checkout scm
              sh '''
                find . -name .git | xargs rm -r
                rm -r deps/k tests/ethereum-tests deps/metropolis
                cd ..
                tar czvf kevm-${KEVM_RELEASE_ID}-src.tar.gz kevm-${KEVM_RELEASE_ID}-src
              '''
            }
            stash name: 'src-kevm', includes: "kevm-${env.KEVM_RELEASE_ID}-src.tar.gz"
          }
        }
        stage('Build Ubuntu Bionic Package') {
          agent {
            dockerfile {
              dir "kevm-${env.KEVM_RELEASE_ID}/package"
              filename 'Dockerfile.ubuntu-bionic'
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
              reuseNode true
            }
          }
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              unstash 'bionic-kframework'
              sh '''
                sudo apt-get update && sudo apt-get upgrade --yes
                sudo apt-get install --yes ./kframework.deb
                cp -r package/debian ./
                dpkg-buildpackage --no-sign
              '''
            }
            stash name: 'bionic-kevm', includes: "kevm_${env.KEVM_RELEASE_ID}_amd64.deb"
          }
        }
        stage('Test Ubuntu Bionic Package') {
          agent {
            dockerfile {
              dir "kevm-${env.KEVM_RELEASE_ID}/package"
              filename 'Dockerfile.ubuntu-bionic'
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
              reuseNode true
            }
          }
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              unstash 'bionic-kevm'
              sh '''
                sudo apt-get update && sudo apt-get upgrade --yes
                sudo apt-get install --yes ./kevm_${KEVM_RELEASE_ID}_amd64.deb
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
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
              reuseNode true
            }
          }
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              unstash 'arch-kframework'
              sh '''
                sudo pacman -Syu --noconfirm
                sudo pacman --noconfirm -U kframework-git.pkg.tar.xz
                cd package
                makepkg --noconfirm --syncdeps
              '''
            }
            stash name: 'arch-kevm', includes: "kevm-${env.KEVM_RELEASE_ID}/package/kevm-git-${env.KEVM_RELEASE_ID}-1-x86_64.pkg.tar.xz"
          }
        }
        stage('Test Arch Package') {
          agent {
            dockerfile {
              dir "kevm-${env.KEVM_RELEASE_ID}/package"
              filename 'Dockerfile.arch'
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
              reuseNode true
            }
          }
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              unstash 'arch-kevm'
              sh '''
                sudo pacman -Syu --noconfirm
                sudo pacman --noconfirm -U package/kevm-git-${KEVM_RELEASE_ID}-1-x86_64.pkg.tar.xz
                make test-interactive-firefly
              '''
            }
          }
        }
        stage('Upload Release') {
          agent {
            dockerfile {
              dir "kevm-${env.KEVM_RELEASE_ID}/package"
              filename 'Dockerfile.arch'
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
              reuseNode true
            }
          }
          steps {
            dir("kevm-${env.KEVM_RELEASE_ID}") {
              unstash 'src-kevm'
              unstash 'bionic-kevm'
              unstash 'arch-kevm'
              sh '''
                release_tag="v${KEVM_RELEASE_ID}-$(git rev-parse --short HEAD)"
                make release.md KEVM_RELEASE_TAG=${release_tag}
                hub release create                                                                                          \
                    --attach "kevm-${KEVM_RELEASE_ID}-src.tar.gz#Source tar.gz"                                             \
                    --attach "kevm_${KEVM_RELEASE_ID}_amd64.deb#Ubuntu Bionic (18.04) Package"                              \
                    --attach "kevm-${KEVM_RELEASE_ID}/package/kevm-git-${KEVM_RELEASE_ID}-1-x86_64.pkg.tar.xz#Arch Package" \
                    --file "release.md" "${release_tag}"
              '''
            }
          }
        }
      }
      post {
        failure {
          slackSend color: '#cb2431'                                 \
                  , channel: '#kevm'                                 \
                  , message: "KEVM Release Failed: ${env.BUILD_URL}"
        }
      }
    }
  }
}
