pipeline {
  agent { label 'docker && big' }
  environment {
    GITHUB_TOKEN     = credentials('rv-jenkins-access-token')
    VERSION          = '1.0.1'
    LONG_REV         = """${sh(returnStdout: true, script: 'git rev-parse HEAD').trim()}"""
    SHORT_REV        = """${sh(returnStdout: true, script: 'git rev-parse --short=7 HEAD').trim()}"""
    KEVM_RELEASE_TAG = "v${env.VERSION}-${env.SHORT_REV}"
    K_VERSION        = """${sh(returnStdout: true, script: 'cd deps/k && git tag --points-at HEAD | cut --characters=2-').trim()}"""
  }
  options { ansiColor('xterm') }
  stages {
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
            dir('focal')  { unstash 'focal'  }
            sshagent(['rv-jenkins-github']) {
              sh '''
                git clone 'ssh://github.com/runtimeverification/evm-semantics.git' kevm-release
                cd kevm-release
                git fetch --all

                git tag -d "${KEVM_RELEASE_TAG}"         || true
                git push -d origin "${KEVM_RELEASE_TAG}" || true
                hub release delete "${KEVM_RELEASE_TAG}" || true

                git tag "${KEVM_RELEASE_TAG}" "${LONG_REV}"
                git push origin "${KEVM_RELEASE_TAG}"

                focal_name=kevm_${VERSION}_amd64_focal.deb
                mv ../focal/kevm_${VERSION}_amd64.deb  ${focal_name}

                echo "KEVM Release ${KEVM_RELEASE_TAG}"  > release.md
                echo ''                                 >> release.md
                cat INSTALL.md                          >> release.md
                hub release create                                          \
                    --attach ${focal_name}'#Ubuntu Focal (20.04) Package'   \
                    --file release.md "${KEVM_RELEASE_TAG}"
              '''
            }
          }
        }
        stage('Jello Paper') {
          steps {
            sshagent(['rv-jenkins-github']) {
              dir("kevm-${env.VERSION}-jello-paper") {
                sh '''
                  git clone 'ssh://github.com/runtimeverification/evm-semantics.git'
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
