pipeline {
  agent { label 'docker && !smol' }
  environment {
    GITHUB_TOKEN     = credentials('rv-jenkins')
    VERSION          = '1.0.1'
    LONG_REV         = """${sh(returnStdout: true, script: 'git rev-parse HEAD').trim()}"""
    SHORT_REV        = """${sh(returnStdout: true, script: 'git rev-parse --short=7 HEAD').trim()}"""
    KEVM_RELEASE_TAG = "v${env.VERSION}-${env.SHORT_REV}"
    K_VERSION        = """${sh(returnStdout: true, script: 'cd deps/k && git tag --points-at HEAD | cut --characters=2-').trim()}"""
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
          additionalBuildArgs '--build-arg K_COMMIT="${K_VERSION}" --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
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
            timeout(time: 120, unit: 'MINUTES')
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
      post { failure { slackSend color: '#cb2431' , channel: '#kevm' , message: "Packaging Phase Failed: ${env.BUILD_URL}" } }
      stages {
        stage('Ubuntu Bionic') {
          stages {
            stage('Build Ubuntu Bionic') {
              agent {
                dockerfile {
                  additionalBuildArgs '--build-arg K_COMMIT="${K_VERSION}" --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
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
                dockerfile {
                  filename 'package/debian/Dockerfile.test'
                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg BASE_IMAGE=ubuntu:bionic'
                  reuseNode true
                }
              }
              options { skipDefaultCheckout() }
              steps {
                dir('bionic-test') {
                  checkout scm
                  unstash 'bionic'
                  sh '''
                    export KLAB_OUT=$(pwd)
                    sudo apt-get update
                    sudo apt-get upgrade --yes
                    sudo apt-get install --yes ./kevm_${VERSION}_amd64.deb
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
        stage('Ubuntu Focal') {
          stages {
            stage('Build Ubuntu Focal') {
              agent {
                dockerfile {
                  additionalBuildArgs '--build-arg K_COMMIT="${K_VERSION}" --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
                  reuseNode true
                }
              }
              steps {
                dir('focal-build') {
                  checkout scm
                  sh './package/debian/package focal'
                }
                stash name: 'focal', includes: "kevm_${env.VERSION}_amd64.deb"
              }
            }
          }
        }
        stage('DockerHub') {
          environment {
            DOCKERHUB_TOKEN    = credentials('rvdockerhub')
            BIONIC_VERSION_TAG = "ubuntu-bionic-${env.SHORT_REV}"
            BIONIC_BRANCH_TAG  = "ubuntu-bionic-${env.BRANCH_NAME}"
            FOCAL_VERSION_TAG  = "ubuntu-focal-${env.SHORT_REV}"
            FOCAL_BRANCH_TAG   = "ubuntu-focal-${env.BRANCH_NAME}"
            DOCKERHUB_REPO     = "runtimeverificationinc/kframework-evm-semantics"
          }
          stages {
            stage('Build Image') {
              agent { label 'docker' }
              steps {
                dir('bionic') { unstash 'bionic' }
                sh '''
                    mv bionic/kevm_${VERSION}_amd64.deb kevm_amd64_bionic.deb
                    docker login --username "${DOCKERHUB_TOKEN_USR}" --password "${DOCKERHUB_TOKEN_PSW}"
                    docker image build . --file package/docker/Dockerfile.ubuntu --tag "${DOCKERHUB_REPO}:${BIONIC_VERSION_TAG}" --build-arg BASE_IMAGE=bionic
                    docker image push "${DOCKERHUB_REPO}:${BIONIC_VERSION_TAG}"
                    docker tag "${DOCKERHUB_REPO}:${BIONIC_VERSION_TAG}" "${DOCKERHUB_REPO}:${BIONIC_BRANCH_TAG}"
                    docker push "${DOCKERHUB_REPO}:${BIONIC_BRANCH_TAG}"
                '''
                dir('focal') { unstash 'focal' }
                sh '''
                    mv focal/kevm_${VERSION}_amd64.deb kevm_amd64_focal.deb
                    docker login --username "${DOCKERHUB_TOKEN_USR}" --password "${DOCKERHUB_TOKEN_PSW}"
                    docker image build . --file package/docker/Dockerfile.ubuntu --tag "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}" --build-arg BASE_IMAGE=focal
                    docker image push "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}"
                    docker tag "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}" "${DOCKERHUB_REPO}:${FOCAL_BRANCH_TAG}"
                    docker push "${DOCKERHUB_REPO}:${FOCAL_BRANCH_TAG}"
                '''
              }
            }
            stage('Test Bionic Image') {
              agent {
                docker {
                  image "${DOCKERHUB_REPO}:${BIONIC_VERSION_TAG}"
                  args '-u 0'
                  reuseNode true
                }
              }
              steps { sh 'which kevm ; kevm help ; kevm version ;' }
            }
            stage('Test Focal Image') {
              agent {
                docker {
                  image "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}"
                  args '-u 0'
                  reuseNode true
                }
              }
              steps { sh 'which kevm ; kevm help ; kevm version ;' }
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
          additionalBuildArgs '--build-arg K_COMMIT="${K_VERSION}" --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          reuseNode true
        }
      }
      post { failure { slackSend color: '#cb2431' , channel: '#kevm' , message: "Deploy Phase Failed: ${env.BUILD_URL}" } }
      stages {
        stage('GitHub Release') {
          steps {
            dir('bionic') { unstash 'bionic' }
            dir('focal')  { unstash 'focal'  }
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

                bionic_name=kevm_${VERSION}_amd64_bionic.deb
                focal_name=kevm_${VERSION}_amd64_focal.deb
                mv ../bionic/kevm_${VERSION}_amd64.deb ${bionic_name}
                mv ../focal/kevm_${VERSION}_amd64.deb  ${focal_name}

                echo "KEVM Release ${KEVM_RELEASE_TAG}"  > release.md
                echo ''                                 >> release.md
                cat INSTALL.md                          >> release.md
                hub release create                                          \
                    --attach ${bionic_name}'#Ubuntu Bionic (18.04) Package' \
                    --attach ${focal_name}'#Ubuntu Focal (20.04) Package'   \
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
