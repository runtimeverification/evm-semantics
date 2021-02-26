pipeline {
  agent { label 'docker && !smol' }
  environment {
    GITHUB_TOKEN = credentials('rv-jenkins')
    VERSION          = '1.0.0'
    K_VERSION        = '5.0.0'
    K_ROOT_URL       = 'https://github.com/kframework/k/releases/download'
    PACKAGE          = 'kevm'
    ROOT_URL         = 'https://github.com/kframework/evm-semantics/releases/download'
    LONG_REV         = """${sh(returnStdout: true, script: 'git rev-parse HEAD').trim()}"""
    SHORT_REV        = """${sh(returnStdout: true, script: 'git rev-parse --short=7 HEAD').trim()}"""
    KEVM_RELEASE_TAG = "v${env.VERSION}-${env.SHORT_REV}"
  }
  options { ansiColor('xterm') }
  stages {
    stage('Init title') {
      when { changeRequest() }
      steps { script { currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}" } }
    }
    stage('Build and Test') {
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg K_COMMIT="$(cd deps/k && git rev-parse --short=7 HEAD)" --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          reuseNode true
        }
      }
      stages {
        stage('Deps')  { steps { sh 'make plugin-deps'            } }
        stage('Build') { steps { sh 'make build RELEASE=true -j6' } }
        stage('Test Execution') {
          failFast true
          options { timeout(time: 25, unit: 'MINUTES') }
          parallel {
            stage('Conformance (LLVM)') { steps { sh 'make test-conformance -j8 TEST_CONCRETE_BACKEND=llvm' } }
            stage('VM (Haskell)')       { steps { sh 'make test-vm -j8 TEST_CONCRETE_BACKEND=haskell'       } }
          }
        }
        stage('Proofs') {
          options {
            lock("proofs-${env.NODE_NAME}")
            timeout(time: 100, unit: 'MINUTES')
          }
          parallel {
            stage('Java')              { steps { sh 'make test-prove -j5 TEST_SYMBOLIC_BACKEND=java'    } }
            stage('Haskell')           { steps { sh 'make test-prove -j4 TEST_SYMBOLIC_BACKEND=haskell' } }
            stage('Haskell (dry-run)') { steps { sh 'make test-haskell-dry-run -j3'                     } }
          }
        }
        stage('Test Interactive') {
          failFast true
          options { timeout(time: 35, unit: 'MINUTES') }
          parallel {
            stage('LLVM krun')      { steps { sh 'make test-interactive-run TEST_CONCRETE_BACKEND=llvm'           } }
            stage('Java krun')      { steps { sh 'make test-interactive-run TEST_CONCRETE_BACKEND=java'           } }
            stage('Haskell krun')   { steps { sh 'make test-interactive-run TEST_CONCRETE_BACKEND=haskell'        } }
            stage('LLVM Kast')      { steps { sh 'make test-parse TEST_CONCRETE_BACKEND=llvm'                     } }
            stage('Failing tests')  { steps { sh 'make test-failure TEST_CONCRETE_BACKEND=llvm'                   } }
            stage('Java KLab')      { steps { sh 'make test-klab-prove TEST_SYMBOLIC_BACKEND=java'                } }
            stage('Haskell Search') { steps { sh 'make test-interactive-search TEST_SYMBOLIC_BACKEND=haskell -j4' } }
            stage('KEVM help')      { steps { sh './kevm help'                                                    } }
          }
        }
      }
    }
    stage('Package') {
      when {
        branch 'master'
        beforeAgent true
      }
      stages {
        stage('Build Ubuntu Bionic') {
          agent {
            dockerfile {
              additionalBuildArgs '--build-arg K_COMMIT="$(cd deps/k && git rev-parse --short=7 HEAD)" --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
              reuseNode true
            }
          }
          steps {
            dir('bionic-build') {
              checkout scm
              sh './package/debian/package bionic'
            }
            stash name: 'bionic', includes: "kevm_${env.VERSION}_amd64.deb"
          }
        }
        stage('Test Ubuntu Bionic') {
          agent {
            docker {
              image 'ubuntu:bionic'
              args '-u 0'
              reuseNode true
            }
          }
          options { skipDefaultCheckout() }
          steps {
            dir('bionic-test') {
              checkout scm
              unstash 'bionic'
              sh '''
                export DEBIAN_FRONTEND=noninteractive
                apt-get update
                apt-get upgrade --yes
                apt-get install --yes git make
                apt-get install --yes ./kevm_${VERSION}_amd64.deb
                which kevm
                kevm help
                kevm version
                make -j4 test-interactive-run    TEST_CONCRETE_BACKEND=llvm
                make -j4 test-interactive-run    TEST_CONCRETE_BACKEND=java
                make -j4 test-interactive-run    TEST_CONCRETE_BACKEND=haskell
                make -j4 test-parse              TEST_CONCRETE_BACKEND=llvm
                make -j4 test-failure            TEST_CONCRETE_BACKEND=llvm
                make -j4 test-klab-prove         TEST_SYMBOLIC_BACKEND=java
                make -j4 test-interactive-search TEST_SYMBOLIC_BACKEND=haskell
              '''
            }
          }
        }
      }
    }
    stage('Deploy') {
      when {
        branch 'master'
        beforeAgent true
      }
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg K_COMMIT="$(cd deps/k && git rev-parse --short=7 HEAD)" --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          reuseNode true
        }
      }
      stages {
        stage('GitHub Release') {
          steps {
            dir('bionic') { unstash 'bionic' }
            sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
              sh '''
                git clone 'ssh://github.com/kframework/evm-semantics.git' kevm-release
                cd kevm-release
                git fetch --all

                git tag -d "${KEVM_RELEASE_TAG}"         || true
                git push -d origin "${KEVM_RELEASE_TAG}" || true
                hub release delete "${KEVM_RELEASE_TAG}" || true

                git tag "${KEVM_RELEASE_TAG}" "${LONG_REV}"
                git push origin "${KEVM_RELEASE_TAG}"

                COMMIT_DATE=$(date '+%Y%m%d%H%M' --date="$(git show --no-patch --format='%ci' ${KEVM_RELEASE_TAG})")

                bionic_name=kevm_${VERSION}_amd64_bionic_${COMMIT_DATE}.deb
                mv ../bionic/kevm_${VERSION}_amd64.deb ${bionic_name}

                echo "KEVM Release ${KEVM_RELEASE_TAG}"  > release.md
                echo ''                                 >> release.md
                cat INSTALL.md                          >> release.md
                hub release create                                          \
                    --attach ${bionic_name}'#Ubuntu Bionic (18.04) Package' \
                    --file release.md "${KEVM_RELEASE_TAG}"
              '''
            }
          }
        }
        stage('Update Dependents') {
          steps {
            build job: 'rv-devops/master', propagate: false, wait: false                                         \
                , parameters: [ booleanParam ( name: 'UPDATE_DEPS'         , value: true                       ) \
                              , string       ( name: 'UPDATE_DEPS_REPO'    , value: 'kframework/evm-semantics' ) \
                              , string       ( name: 'UPDATE_DEPS_VERSION' , value: "${env.LONG_REV}")           \
                              ]
          }
        }
        stage('Jello Paper') {
          steps {
            sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
              dir("kevm-${env.VERSION}-jello-paper") {
                sh '''
                  git clone 'ssh://github.com/kframework/evm-semantics.git'
                  cd evm-semantics
                  git checkout -B gh-pages origin/master
                  git submodule update --init --recursive -- ./web
                  cd web
                  npm install
                  npm run build
                  npm run build-sitemap
                  cd -
                  mv web/public_content ./
                  rm -rf $(find . -maxdepth 1 -not -name public_content -a -not -name .git -a -not -path . -a -not -path .. -a -not -name CNAME)
                  mv public_content/* ./
                  rm -rf public_content
                  git add ./
                  git commit -m 'gh-pages: Updated the website'
                  git merge --strategy ours origin/gh-pages --allow-unrelated-histories
                  git push origin gh-pages
                '''
              }
            }
          }
        }
      }
    }
  }
}
